import os
import sys
import time
import collections
import random
import json
import base64
import hashlib
from datetime import datetime, tzinfo, timedelta

from noise.connection import NoiseConnection, Keypair
import hid

from .usb import hid_send_frames, hid_read_frames

try:
    from .generated import hww_pb2 as hww
except ModuleNotFoundError:
    print('Run `make messages` to generate the protobuf messages')
    sys.exit()

U2F_CID_BROADCAST = 0xffffffff

U2F_PING_CMD = 0x80 | 0x01
U2F_INIT_CMD = 0x80 | 0x06
U2F_WINK_CMD = 0x80 | 0x08
U2F_MSG_CMD = 0x80 | 0x03

def get_bitbox02u2f_devices():
    # TODO: product id is 0x2403, but 0x2402 is the id of some dev
    # device bootloaders. Can be removed in time, not needed for
    # production devices.
    return [info for info in hid.enumerate()
            if info['vendor_id'] == 0x03eb and
            info['product_id'] in (0x2402, 0x2403) and
            (info['usage_page'] == 0xffff or
             info['interface_number'] == 1)]


class Bitbox02Exception(Exception):
    def __init__(self, code, message):
        self.code = code
        self.message = message

    def __str__(self):
        return f"error code: {self.code}, message: {self.message}"

class APDU:
    def __init__(self, ins, p1, p2, length, data):
        """
        Sets up the APDU packet.
        ins: command code, 1: register, 2: authenticate, 3: version
        p1: parameters for the command, for authenticate:
            0x07: check-only
            0x03: enforce-user-presence-and-sign
            0X08: dont-enforce-user-presence-and-sign
        """
        self._apdubytes = bytearray()
        self._apdubytes.append(0)
        self._apdubytes.append(ins)
        self._apdubytes.append(p1)
        self._apdubytes.append(p2)
        self._apdubytes.append((length >> 16) & 0xFF)
        self._apdubytes.append((length >> 8) & 0xFF)
        self._apdubytes.append((length >> 0) & 0xFF)
        self._apdubytes.extend(data);
    def __bytes__(self):
        return self._apdubytes

def _random_32():
    random_bytes = bytearray(32)
    for i in range(0,32):
        random_bytes[i] = round(random.uniform(0, 255))
    return random_bytes

class RegistrationResponse:
    def __init__(self, response_bytes):
        """
        Creates an registration response.
        """
        self.register_id = response_bytes[0]
        self.ec_public_key = response_bytes[1:66]
        self.key_handle_length = response_bytes[66]
        limit = 67 + self.key_handle_length
        self.key_handle = response_bytes[67:limit]


class RegistrationRequest:
    def __init__(self, app_id):
        """
        Creates an APDU packet for request.
        """
        client_data = {'typ':'navigator.id.finishEnrollment', 'challenge': base64.b64encode(_random_32()).decode('utf-8'), 'origin': app_id}
        client_data_hash = hashlib.sha256()
        client_data_hash.update(json.dumps(client_data).encode('utf-8'))
        challenge_parameter = client_data_hash.digest()
        app_id_hash = hashlib.sha256()
        app_id_hash.update(app_id.encode('utf-8'))
        app_parameter = app_id_hash.digest()
        data = bytearray(64)
        for i in range(0, 32):
            data[i] = challenge_parameter[i]
        for i in range(0, 32):
            data[32 + i] = app_parameter[i]
        self._apdu = APDU(0x01, 0x00, 0x00, len(data), data)

    def send(self, bitbox02_u2f):
        response_bytes = bitbox02_u2f.u2f_msg(self._apdu.__bytes__())
        print(f'response bytes: {response_bytes}')
        return RegistrationResponse(response_bytes)

class AuthenticationResponse:
    def __init__(self, response_bytes):
        """
        Creates an authentication response.
        """
        self.flags = response_bytes[0]
        self.ctr = response_bytes[1:5]
        self.sig = response_bytes[5:]


class AuthenticationRequest:
    def __init__(self, app_id, key_handle_length, key_handle):
        """
        Creates an APDU packet for request.
        """
        data = bytearray()
        # control byte 0x03: enforce-user-presence-and-sign
        data.append(0x03)
        client_data = {'typ':'navigator.id.getAssertion', 'challenge': base64.b64encode(_random_32()).decode('utf-8'), 'origin': app_id}
        client_data_hash = hashlib.sha256()
        client_data_hash.update(json.dumps(client_data).encode('utf-8'))
        challenge_parameter = client_data_hash.digest()
        data.extend(challenge_parameter)
        app_id_hash = hashlib.sha256()
        app_id_hash.update(app_id.encode('utf-8'))
        app_parameter = app_id_hash.digest()
        data.extend(app_parameter)
        data.append(key_handle_length)
        data.extend(key_handle)

        self._apdu = APDU(0x01, 0x00, 0x00, len(data), data)

    def send(self, bitbox02_u2f):
        response_bytes = bitbox02_u2f.u2f_msg(self._apdu.__bytes__())
        return AuthenticationResponse(response_bytes)



class BitBox02U2F:

    def __init__(self, device_path):
        self.device = hid.device()
        self.device.open_path(device_path)
        self._cid = U2F_CID_BROADCAST

    def close(self):
        self.device.close()

    def _query(self, cid, cmd, msg):
        """
        Sends msg bytes and retrieves response bytes.
        """
        hid_send_frames(self.device, msg, cid, cmd)
        response_bytes = hid_read_frames(self.device, cid, cmd)
        return bytes(response_bytes).rstrip(b'\0')

    def _maybe_error(self, response_bytes, cmd):
        if cmd == 0x80 + 0x3f:
            raise Bitbox02Exception(response_bytes[0], "U2F error discovered")

    def _parse_u2f_init_response(self, response_bytes):
        U2FInitResponse = collections.namedtuple('U2FInitResponse', ['nonce', 'cid', 'versionInterface', 'versionMajor', 'versionMinor', 'versionBuild', 'capFlags'])
        return U2FInitResponse(response_bytes[0:8], response_bytes[8:12], response_bytes[12:13], response_bytes[13:14], response_bytes[14:15], response_bytes[15:16], response_bytes[16:17])

    def u2f_init(self):
        nonce = [1, 2, 3, 4, 5, 6, 7, 8]
        response_bytes = self._query(U2F_CID_BROADCAST, U2F_INIT_CMD, nonce)
        print(f"response: {response_bytes.hex()}")
        init_response = self._parse_u2f_init_response(response_bytes)
        print(f"nonce: {init_response.nonce.hex()}")
        print(f"new cid: {init_response.cid.hex()}")
        self._cid = int.from_bytes(init_response.cid, 'big');
        print(f"version: {str(init_response.versionMajor.decode())} {str(init_response.versionMinor.decode())} {init_response.versionBuild.decode()}")

    def u2f_ping(self):
        echo_msg = bytes('Hello, World!', 'utf-8')
        response_bytes = self._query(self._cid, U2F_PING_CMD, echo_msg)
        if response_bytes == echo_msg:
            return True
        else:
            return False

    def u2f_wink(self):
        print(f"wink wink")
        response_bytes = self._query(self._cid, U2F_WINK_CMD, bytes('', 'utf-8'))

    def u2f_msg(self, msg):
        return self._query(self._cid, U2F_MSG_CMD, msg)


