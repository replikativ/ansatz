#include <lean/lean.h>

/* The release leanc sysroot omits stdio.h; use printf's standard declaration. */
extern int printf(const char *format, ...);

void lean_initialize_runtime_module(void);

int main(void) {
    lean_initialize_runtime_module();
    uint32_t endian = 1;
    int little = *((uint8_t *)&endian) == 1;
    lean_object *small = lean_box_uint32(UINT32_MAX);
    lean_object *wide = lean_box_uint64(UINT64_MAX);
    lean_object *word = lean_box_usize(SIZE_MAX);
    int small_immediate = lean_is_scalar(small);
    int wide_heap = !lean_is_scalar(wide);
    int word_heap = !lean_is_scalar(word);
    uint64_t wide_as_word = (uint64_t)lean_unbox_usize(wide);
    uint64_t word_as_wide = lean_unbox_uint64(word);
    printf("{\"wordBits\":%zu,\"littleEndian\":%s,\"uint32Immediate\":%s,"
           "\"uint64Heap\":%s,\"usizeHeap\":%s,\"wideAsWord\":%llu"
           ",\"wordAsWide\":%llu}\n",
           sizeof(void *) * 8, little ? "true" : "false", small_immediate ? "true" : "false",
           wide_heap ? "true" : "false", word_heap ? "true" : "false",
           (unsigned long long)wide_as_word, (unsigned long long)word_as_wide);
    lean_dec(small);
    lean_dec(wide);
    lean_dec(word);
    return sizeof(void *) == 8 && little && small_immediate && wide_heap && word_heap &&
           wide_as_word == UINT64_MAX && word_as_wide == UINT64_MAX ? 0 : 1;
}
