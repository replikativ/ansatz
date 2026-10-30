/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stdint.h>
#include <stddef.h>

static inline uint64_t lean_uint8_to_uint64(uint8_t a) { return ((uint64_t)a); }
static inline uint64_t lean_uint32_to_uint64(uint32_t a) { return ((uint64_t)a); }
static inline uint64_t lean_usize_to_uint64(size_t a) { return ((uint64_t)a); }
