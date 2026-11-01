#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
/* Exact pinned lean.h body; this oracle does not invoke the Lean frontend. */
static inline uint32_t lean_uint64_to_uint32(uint64_t a) { return ((uint32_t)a); }
int main(void) {
    const uint64_t values[] = {0, 1, UINT64_C(4294967295), UINT64_C(4294967296),
        UINT64_C(4294967297), UINT64_C(9223372036854775807),
        UINT64_C(9223372036854775808), UINT64_C(18446744073709551615)};
    puts("[");
    for (unsigned i = 0; i < sizeof(values)/sizeof(values[0]); ++i)
        printf("[\"%" PRIu64 "\",\"%" PRIu32 "\"]%s\n", values[i],
               lean_uint64_to_uint32(values[i]), i == 7 ? "" : ",");
    puts("]");
    return 0;
}
