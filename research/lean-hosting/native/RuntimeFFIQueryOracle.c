#include <lean/lean.h>
/* Build metadata only. This executes no C compiler or linker.
 * leanc +leanprover/lean4:v4.33.1 -o target/runtime-ffi-query-oracle native/RuntimeFFIQueryOracle.c
 * target/runtime-ffi-query-oracle
 * Hex encodes exact UTF8 including spaces, quotes and ROOT placeholders.
 */
extern int printf(const char *, ...);
void lean_initialize_runtime_module(void);
lean_object *lean_get_leanc_extra_flags(lean_object *);
lean_object *lean_get_leanc_internal_flags(lean_object *);
lean_object *lean_get_internal_linker_flags(lean_object *);
lean_object *lean_get_linker_flags(uint8_t);
lean_object *lean_internal_get_build_type(lean_object *);
static void emit(const char *symbol,const char *selector,lean_object *value) {
 printf("{\"symbol\":\"%s\",\"selector\":\"%s\",\"utf8Hex\":\"",symbol,selector);
 const unsigned char *p=(const unsigned char*)lean_string_cstr(value);
 for(size_t i=0;i<lean_string_size(value)-1;++i)printf("%02x",p[i]);
 printf("\"}\n");lean_dec(value);
}
int main(void) {
 lean_initialize_runtime_module();lean_object *u=lean_box(0);
 emit("lean_get_leanc_extra_flags","unit",lean_get_leanc_extra_flags(u));
 emit("lean_get_leanc_internal_flags","unit",lean_get_leanc_internal_flags(u));
 emit("lean_get_internal_linker_flags","unit",lean_get_internal_linker_flags(u));
 emit("lean_get_linker_flags","static",lean_get_linker_flags(1));
 emit("lean_get_linker_flags","shared",lean_get_linker_flags(0));
 emit("lean_get_linker_flags","nonzero",lean_get_linker_flags(2));
 emit("lean_internal_get_build_type","unit",lean_internal_get_build_type(u));
 return 0;
}
