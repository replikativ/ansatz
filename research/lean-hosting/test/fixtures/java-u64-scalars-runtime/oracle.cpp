// Arithmetic-only oracle: exact pinned inline bodies in pinned-inline.h.
// This is not a complete native Lean object/IR/runtime ABI oracle.
#include "pinned-inline.h"
#include <iostream>
int main() {
    unsigned flag;
    uint64_t a,b;
    while (std::cin >> flag >> a >> b) {
        if (flag > 1) return 2;
        std::cout << flag << ' ' << a << ' ' << b
            << ' ' << lean_bool_to_uint64(static_cast<uint8_t>(flag))
            << ' ' << lean_uint64_add(a,b) << ' ' << lean_uint64_sub(a,b)
            << ' ' << lean_uint64_mul(a,b) << ' ' << lean_uint64_div(a,b)
            << ' ' << lean_uint64_mod(a,b) << ' ' << lean_uint64_land(a,b)
            << ' ' << lean_uint64_lor(a,b) << ' ' << lean_uint64_complement(a)
            << ' ' << lean_uint64_neg(a) << ' ' << lean_uint64_log2(a)
            << ' ' << lean_uint64_shift_left(a,b)
            << ' ' << static_cast<unsigned>(lean_uint64_dec_le(a,b)) << '\n';
    }
    return std::cin.eof() ? 0 : 3;
}
