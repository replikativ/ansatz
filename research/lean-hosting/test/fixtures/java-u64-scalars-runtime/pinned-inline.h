/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stdint.h>

static inline uint64_t lean_bool_to_uint64(uint8_t a) { return (uint64_t)a; }
static inline uint64_t lean_uint64_add(uint64_t a1, uint64_t a2) { return a1+a2; }
static inline uint64_t lean_uint64_sub(uint64_t a1, uint64_t a2) { return a1-a2; }
static inline uint64_t lean_uint64_mul(uint64_t a1, uint64_t a2) { return 1U*a1*a2; }
static inline uint64_t lean_uint64_div(uint64_t a1, uint64_t a2) { return a2 == 0 ? 0  : a1/a2; }
static inline uint64_t lean_uint64_mod(uint64_t a1, uint64_t a2) { return a2 == 0 ? a1 : a1%a2; }
static inline uint64_t lean_uint64_land(uint64_t a, uint64_t b) { return a & b; }
static inline uint64_t lean_uint64_lor(uint64_t a, uint64_t b) { return a | b; }
static inline uint64_t lean_uint64_complement(uint64_t a) { return ~a; }
static inline uint64_t lean_uint64_neg(uint64_t a) { return -a; }
static inline uint64_t lean_uint64_log2(uint64_t a) {
    uint64_t res = 0;
    while (a >= 2) {
        res++;
        a /= 2;
    }
    return res;
}
static inline uint64_t lean_uint64_shift_left(uint64_t a, uint64_t b) { return a << (b % 64); }
static inline uint8_t lean_uint64_dec_le(uint64_t a1, uint64_t a2) { return a1 <= a2; }
