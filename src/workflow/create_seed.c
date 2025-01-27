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

#include "create_seed.h"
#include "password.h"
#include "unlock.h"

#include "keystore.h"
#include "util.h"

#include <string.h>

static uint8_t _host_entropy[32] = {0};

static bool _create_seed_and_unlock(const char* password)
{
    bool result = keystore_create_and_store_seed(password, _host_entropy);
    util_zero(_host_entropy, sizeof(_host_entropy));
    if (!result) {
        return false;
    }
    workflow_unlock_enter_done(password);
    return true;
}

bool workflow_create_seed(const uint8_t* host_entropy)
{
    memcpy(_host_entropy, host_entropy, KEYSTORE_SEED_LENGTH);
    return password_set(_create_seed_and_unlock);
}
