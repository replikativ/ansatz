// Exact pinned inline casts; local input/output scaffolding only.
#include "pinned-inline.h"
#include <iostream>
static_assert(sizeof(size_t)==8,"fixed 64-bit USize profile");
int main() {
    unsigned lane; uint64_t input;
    while (std::cin >> lane >> input) {
        uint64_t result;
        if (lane==8 && input<=UINT8_MAX) result=lean_uint8_to_uint64(static_cast<uint8_t>(input));
        else if (lane==32 && input<=UINT32_MAX) result=lean_uint32_to_uint64(static_cast<uint32_t>(input));
        else if (lane==64) result=lean_usize_to_uint64(static_cast<size_t>(input));
        else return 2;
        std::cout << lane << ' ' << input << ' ' << result << '\n';
    }
    return std::cin.eof()?0:3;
}
