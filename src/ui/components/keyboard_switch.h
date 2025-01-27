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

#ifndef _KEYBOARD_SWITCH_H_
#define _KEYBOARD_SWITCH_H_

#include <ui/component.h>

typedef enum { DIGITS, LOWER_CASE, UPPER_CASE, NUM_INPUT_TYPES } keyboard_mode_t;

/********************************** Create Instance **********************************/

/**
 * Creates a keyboard switch component.
 * @param[in] location The slider location.
 * @param[in] parent The parent component.
 */
component_t* keyboard_switch_create(slider_location_t location, component_t* parent);

#endif
