// Copyright 2019 Shift Cryptosecurity AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef _MOCK_MOCK_H_
#define _MOCK_MOCK_H_

#include <stdbool.h>
#include <stdint.h>

bool memory_write_to_address_mock(uint32_t addr, uint8_t* chunk);
bool memory_write_chunk_mock(uint32_t chunk_num, uint8_t* chunk);
void memory_read_chunk_mock(uint32_t chunk_num, uint8_t* chunk_out);
void memory_read_shared_bootdata_mock(uint8_t* chunk_out);
#endif
