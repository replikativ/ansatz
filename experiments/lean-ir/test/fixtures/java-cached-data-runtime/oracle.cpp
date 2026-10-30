// Local storage scaffolding only. Algorithm bodies in pinned-inline.h are verbatim.
// This models the byte offset, not complete Lean allocation/object/RC ABI.
#include <stdint.h>
#include <stddef.h>
#include <cassert>
#include <iostream>
struct lean_object { unsigned objects; alignas(uint64_t) uint64_t payload[6]; };
using lean_obj_arg=lean_object*;
using b_lean_obj_arg=lean_object*;
static inline unsigned lean_ctor_num_objs(lean_object* o) { return o->objects; }
static inline lean_object** lean_ctor_obj_cptr(lean_object* o) {
    return reinterpret_cast<lean_object**>(o->payload);
}
#include "pinned-inline.h"
static_assert(sizeof(void*)==8,"fixed64-bit object field offset");
int main() {
    unsigned objects; uint64_t word,tail;
    while (std::cin >> objects >> word >> tail) {
        if (objects<1 || objects>4) return 2;
        lean_object o{}; o.objects=objects;
        for (unsigned i=0;i<objects;i++) o.payload[i]=UINT64_C(0x0123456789abcdef);
        o.payload[objects]=word; o.payload[objects+1]=tail;
        const uint64_t before=o.payload[objects+1];
        const uint64_t result=lean_expr_data(&o);
        if (o.payload[objects]!=word || o.payload[objects+1]!=before) return 3;
        std::cout << objects << ' ' << word << ' ' << tail << ' ' << result << '\n';
    }
    return std::cin.eof()?0:4;
}
