#include <lean/lean.h>
#include <stdio.h>

/* Equality returns an unboxed UInt8, unlike the UInt64/USize operands. */
int main(void) {
    const uint64_t values[] = {
        0, 1, UINT64_C(2147483647), UINT64_C(2147483648),
        UINT64_C(4294967295), UINT64_C(4294967296),
        UINT64_C(9223372036854775807), UINT64_C(9223372036854775808), UINT64_MAX
    };
    if (sizeof(size_t) != 8) return 1;
    printf("{\"kind\":\"profile\",\"wordBits\":64,\"cases\":162}\n");
    for (size_t i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
        for (size_t j = 0; j < sizeof(values) / sizeof(values[0]); ++j) {
            uint64_t a = values[i], b = values[j];
            printf("{\"symbol\":\"lean_uint64_dec_eq\",\"a\":\"%llu\",\"b\":\"%llu\",\"result\":\"%u\"}\n",
                   (unsigned long long)a, (unsigned long long)b,
                   (unsigned)lean_uint64_dec_eq(a, b));
            printf("{\"symbol\":\"lean_usize_dec_eq\",\"a\":\"%llu\",\"b\":\"%llu\",\"result\":\"%u\"}\n",
                   (unsigned long long)a, (unsigned long long)b,
                   (unsigned)lean_usize_dec_eq((size_t)a, (size_t)b));
        }
    }
    return 0;
}
