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

#include "reset.h"

#include "hardfault.h"
#include "memory.h"
#ifndef TESTING
#include "securechip/securechip.h"
#endif

void reset_reset(void)
{
    if (!memory_reset_hww()) {
        Abort("Could not reset memory.");
    }
#ifndef TESTING
    if (!securechip_update_keys()) {
        Abort("Could not reset secure chip.");
    }
#endif
}
