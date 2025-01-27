# Copyright 2019 Shift Cryptosecurity AG
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
""" Interact with a BitBox02 bootloader. """

import struct
import typing
import io
import math
import hashlib

import hid
from .usb import hid_send_frames, hid_read_frames

BOOTLOADER_CMD = 0x80 + 0x40 + 0x03
NUM_ROOT_KEYS = 3
NUM_SIGNING_KEYS = 3

MAX_FIRMWARE_SIZE = 884736  # 928kB - 64kB
CHUNK_SIZE = 4096
# max number of chunks that can be written when flashing the firmware
assert MAX_FIRMWARE_SIZE % CHUNK_SIZE == 0
FIRMWARE_CHUNKS = MAX_FIRMWARE_SIZE // CHUNK_SIZE

SIGDATA_MAGIC = struct.pack(">I", 0x653F362B)
MAGIC_LEN = 4

VERSION_LEN = 4
SIGNING_PUBKEYS_DATA_LEN = VERSION_LEN + NUM_SIGNING_KEYS * 64 + NUM_ROOT_KEYS * 64
FIRMWARE_DATA_LEN = VERSION_LEN + NUM_SIGNING_KEYS * 64
SIGDATA_LEN = SIGNING_PUBKEYS_DATA_LEN + FIRMWARE_DATA_LEN


def parse_signed_firmware(firmware: bytes) -> typing.Tuple[bytes, bytes]:
    if len(firmware) < MAGIC_LEN + SIGDATA_LEN:
        raise ValueError("firmware too small")
    magic, firmware = firmware[:MAGIC_LEN], firmware[MAGIC_LEN:]
    if magic != SIGDATA_MAGIC:
        raise ValueError("invalid magic")

    sigdata, firmware = firmware[:SIGDATA_LEN], firmware[SIGDATA_LEN:]
    return sigdata, firmware


class Bootloader:
    """
    One instance of a BitBox02 Bootloader, exposing the bootloader API.
    """

    def __init__(self, device_info):
        self.device = hid.device()
        self.device.open_path(device_info["path"])

    def _query(self, msg: bytes):
        hid_send_frames(self.device, msg, cmd=BOOTLOADER_CMD)
        response = bytes(hid_read_frames(self.device, cmd=BOOTLOADER_CMD))
        if response[0] != msg[0]:
            raise Exception("bootloader api error, expected {}, got {}".format(msg[0], response[0]))
        if response[1] != 0:
            raise Exception("bootloader api error: code={}".format(response[1]))
        return response[2:]

    def versions(self) -> typing.Tuple[int, int]:
        """
        Returns (firmware version, signing pubkeys version).
        """
        response = self._query(b"v")
        firmware_v, signing_pubkeys_v = struct.unpack("<II", response[:8])
        return firmware_v, signing_pubkeys_v

    def get_hashes(
        self, display_firmware_hash: bool = False, display_signing_keydata_hash: bool = False
    ) -> typing.Tuple[bytes, bytes]:
        """
        Returns (firmare hash, signing keydata hash).
        If display is True, the hash is shown on the device screen.
        """
        response = self._query(
            b"h" + bytes([int(display_firmware_hash), int(display_signing_keydata_hash)])
        )
        firmware_hash, signing_keydata_hash = response[:32], response[32:64]
        return firmware_hash, signing_keydata_hash

    def show_firmware_hash_enabled(self) -> bool:
        """
        Returns whether the bootloader will automatically show the firmware hash on boot.
        """
        return bool(self._query(b"H\xFF")[0])

    def set_show_firmware_hash(self, enable: bool) -> bool:
        """
        Enables/disables whether the bootloader will automatically show the firmware hash on boot.
        """
        self._query(b"H" + bytes([int(enable)]))

    def _erase(self, firmware_num_chunks: int):
        self._query(b"e" + bytes([firmware_num_chunks]))

    def _write_chunk(self, chunk_num: int, chunk: bytes):
        if len(chunk) != CHUNK_SIZE:
            raise ValueError("chunk must be 4kB")
        self._query(b"w" + bytes([chunk_num]) + chunk)

    def flash_unsigned_firmware(
        self, firmware: bytes, progress_callback: typing.Callable[[float], None] = None
    ):
        """
        Flashes a firmware image onto the bootloader by invoking the erase and write chunk api
        calls. Expects the raw firmware without signatures, and does not flash the signatures.
        """
        if len(firmware) > FIRMWARE_CHUNKS * CHUNK_SIZE:
            raise ValueError("firmware too big")
        if progress_callback is not None:
            progress_callback(0)
        num_chunks = math.ceil(len(firmware) / CHUNK_SIZE)
        self._erase(num_chunks)
        stream = io.BytesIO(firmware)
        chunk_num = 0
        while True:
            chunk = stream.read(CHUNK_SIZE)
            if not chunk:
                break
            if len(chunk) < CHUNK_SIZE:
                chunk += b"\xff" * (CHUNK_SIZE - len(chunk))
            self._write_chunk(chunk_num, chunk)
            chunk_num += 1
            if progress_callback is not None:
                progress_callback(chunk_num / num_chunks)

    def flash_signed_firmware(
        self, firmware: bytes, progress_callback: typing.Callable[[float], None] = None
    ):
        """
        Flashes a signed firmware image. The firmware itself is extracted and flashed, then the
        signatures are extracted and flashed.
        """

        sigdata, firmware = parse_signed_firmware(firmware)
        self.flash_unsigned_firmware(firmware, progress_callback=progress_callback)
        self._query(b"s" + sigdata)

    def erase(self):
        """
        Erases the firmware from the device.
        """
        self._erase(0)

    def erased(self) -> bool:
        """
        Returns True if the the device contains no firmware.
        """
        # We check by comparing the device reported firmware hash. If erased, the firmware is all '\xFF'.
        firmware_v, _ = self.versions()
        empty_firmware = struct.pack("<I", firmware_v) + b"\xFF" * MAX_FIRMWARE_SIZE
        empty_firmware_hash = hashlib.sha256(hashlib.sha256(empty_firmware).digest()).digest()
        reported_firmware_hash, _ = self.get_hashes()
        return empty_firmware_hash == reported_firmware_hash

    def reboot(self):
        hid_send_frames(self.device, b"r", cmd=BOOTLOADER_CMD)
        self.device.close()

    def screen_rotate(self):
        self._query(b"f")

    def close(self):
        self.device.close()
