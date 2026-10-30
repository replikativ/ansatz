/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

static inline uint64_t lean_ctor_get_uint64(b_lean_obj_arg o, unsigned offset) {
    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));
    return *((uint64_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));
}
static inline uint64_t lean_expr_data(lean_obj_arg expr) {
    return lean_ctor_get_uint64(expr, lean_ctor_num_objs(expr)*sizeof(void*));
}
