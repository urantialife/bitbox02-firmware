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
"""USB device utility functions"""

import re

import hid
import semver

BOOTLOADER = "bb02-bootloader"
BITBOX02 = "BitBox02"


def get_bitbox02_devices(product_string=BITBOX02):
    """
    Scans devices and returns a list of hid device info objects.
    """
    # TODO: product id is 0x2403, but 0x2402 is the id of some dev
    # device bootloaders. Can be removed in time, not needed for
    # production devices.
    return [
        info
        for info in hid.enumerate()
        if info["vendor_id"] == 0x03EB
        and info["product_id"] in (0x2402, 0x2403)
        and (info["usage_page"] == 0xFFFF or info["interface_number"] == 0)
        and info["product_string"] == product_string
    ]


def parse_device_version(serial_number):
    match = re.search(r"v([0-9]+\.[0-9]+\.[0-9]+.*)", serial_number)
    if match is None:
        return None

    return semver.VersionInfo.parse(match.group(1))
