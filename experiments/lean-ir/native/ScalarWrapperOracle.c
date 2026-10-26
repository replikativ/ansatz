#include <lean/lean.h>
#include <stdio.h>

/* Compile against the pinned Lean release header, rather than reproducing its
 * arithmetic in the host test. Decimal strings preserve all unsigned bits. */
int main(void) {
    const uint64_t values[] = {
        0, 1, UINT64_C(2147483647), UINT64_C(2147483648),
        UINT64_C(4294967295), UINT64_C(4294967296),
        UINT64_C(9223372036854775807), UINT64_C(9223372036854775808), UINT64_MAX
    };
    const char *symbols[] = {
        "lean_uint64_add", "lean_uint64_sub", "lean_usize_add", "lean_usize_sub"
    };
    if (sizeof(size_t) != 8) return 1;
    printf("{\"kind\":\"profile\",\"wordBits\":64,\"cases\":324}\n");
    for (size_t i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
        for (size_t j = 0; j < sizeof(values) / sizeof(values[0]); ++j) {
            uint64_t a = values[i], b = values[j];
            uint64_t results[] = {
                lean_uint64_add(a, b), lean_uint64_sub(a, b),
                (uint64_t)lean_usize_add((size_t)a, (size_t)b),
                (uint64_t)lean_usize_sub((size_t)a, (size_t)b)
            };
            for (size_t k = 0; k < 4; ++k) {
                printf("{\"symbol\":\"%s\",\"a\":\"%llu\",\"b\":\"%llu\",\"result\":\"%llu\"}\n",
                       symbols[k], (unsigned long long)a, (unsigned long long)b,
                       (unsigned long long)results[k]);
            }
        }
    }
    return 0;
}
