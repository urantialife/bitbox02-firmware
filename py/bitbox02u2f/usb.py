import struct

USB_REPORT_SIZE = 64


def hid_send_frames(hid_device, data, cid, cmd):
    data = bytearray(data)
    data_len = len(data)
    seq = 0
    idx = 0;
    write = []
    write_empty = data_len == 0
    while idx < data_len or write_empty:
        if idx == 0:
            # INIT frame
            write = data[idx: idx + min(data_len, USB_REPORT_SIZE - 7)]
            hid_device.write(
                b'\0' + struct.pack(">IBH", cid, cmd, data_len & 0xFFFF) +
                write + b'\xEE' * (USB_REPORT_SIZE - 7 - len(write)))
        else:
            # CONT frame
            write = data[idx: idx + min(data_len, USB_REPORT_SIZE - 5)]
            hid_device.write(
                b'\0' + struct.pack(">IB", cid, seq) +
                write + b'\xEE' * (USB_REPORT_SIZE - 5 - len(write)))
            seq += 1
        idx += len(write)
        write_empty = False

def _throw_error(error_code):
    if error_code == 0x01:
        raise Exception('Received error: invalid command')
    elif error_code == 0x03:
        raise Exception('Received error: invalid length')
    elif error_code == 0x04:
        raise Exception('Received error: invalid sequence')
    elif error_code == 0x06:
        raise Exception('Received error: channel busy')
    elif error_code == 0x7e:
        raise Exception('Received error: encryption failed')
    elif error_code == 0x7f:
        raise Exception('Received unknown error')
    else:
        raise Exception('Received error: %d' % error_code)

def hid_read_frames(hid_device, cid, cmd, timeout=5000):
    timeout_ms = timeout * 1000
    read = hid_device.read(USB_REPORT_SIZE, timeout_ms)
    if len(read) >= 3:
        reply_cid = ((read[0] * 256 + read[1]) * 256 + read[2]) * 256 + read[3]
        reply_cmd = read[4]
        data_len = read[5] * 256 + read[6]
        data = read[7:]
        idx = len(read) - 7
        if reply_cmd == 0x80 + 0x3f:
            _throw_error(data[0])

        while idx < data_len:
            # CONT response
            read = hid_device.read(USB_REPORT_SIZE, timeout_ms)
            if len(read) < 3:
                raise Exception(
                    'Did not receive a continuation frame after %d seconds' %
                    timeout)
            data += read[5:]
            idx += len(read) - 5
        assert reply_cid == cid, '- USB channel ID mismatch'
        assert reply_cmd == cmd, '- USB command id mismatch'
        return data
    raise Exception('Did not read anything after %d seconds' % timeout)
