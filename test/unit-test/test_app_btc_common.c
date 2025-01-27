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

#include <setjmp.h>
#include <stdarg.h>
#include <stddef.h>
#include <cmocka.h>

#include <apps/btc/btc_common.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-prototypes"
#pragma GCC diagnostic ignored "-Wunused-parameter"

static void _test_btc_common_format_amount_invalid_params(void** state)
{
    char out[100] = {0};

    assert_false(btc_common_format_amount(0, "", NULL, sizeof(out)));
    for (size_t wrong_out_len = 0; wrong_out_len < 30; wrong_out_len++) {
        assert_false(btc_common_format_amount(0, "", out, wrong_out_len));
    }
    assert_true(btc_common_format_amount(0, "", out, 31));
}

typedef struct {
    uint64_t satoshi;
    const char* out;
} btc_format_test_t;

static void _test_btc_common_format_amount(void** state)
{
    const btc_format_test_t tests[] = {
        {0, "0 LOL"},
        {1, "0.00000001 LOL"},
        {2, "0.00000002 LOL"},
        {10, "0.0000001 LOL"},
        {15, "0.00000015 LOL"},
        {20, "0.0000002 LOL"},
        {300, "0.000003 LOL"},
        {370, "0.0000037 LOL"},
        {371, "0.00000371 LOL"},
        {40000000000, "400 LOL"},
        {4000000000, "40 LOL"},
        {400000000, "4 LOL"},
        {40000000, "0.4 LOL"},
        {4000000, "0.04 LOL"},
        {400000, "0.004 LOL"},
        {40000, "0.0004 LOL"},
        {4000, "0.00004 LOL"},
        {400, "0.000004 LOL"},
        {40, "0.0000004 LOL"},
        {4, "0.00000004 LOL"},
        {5432345, "0.05432345 LOL"},
        {54323452, "0.54323452 LOL"},
        {543234527, "5.43234527 LOL"},
        {5432345270, "54.3234527 LOL"},
        {54323452708, "543.23452708 LOL"},
        {100000000, "1 LOL"},
        {1234567800000001, "12345678.00000001 LOL"},
        {0xffffffffffffffff, "184467440737.09551615 LOL"},
        {0xffffffffffffffff - 5, "184467440737.0955161 LOL"},
    };
    for (unsigned int i = 0; i < sizeof(tests) / sizeof(btc_format_test_t); i++) {
        const btc_format_test_t* test = &tests[i];
        char out[100] = {0};
        assert_true(btc_common_format_amount(test->satoshi, "LOL", out, sizeof(out)));
        assert_string_equal(test->out, out);
    }
}

int main(void)
{
    const struct CMUnitTest tests[] = {
        cmocka_unit_test(_test_btc_common_format_amount_invalid_params),
        cmocka_unit_test(_test_btc_common_format_amount),
    };
    return cmocka_run_group_tests(tests, NULL, NULL);
}

#pragma GCC diagnostic pop
