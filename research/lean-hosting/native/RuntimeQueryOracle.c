#include <lean/lean.h>
/* Exact release build metadata, not a universal Lean version table.
 * Reproduce:
 * leanc +leanprover/lean4:v4.33.1 -o target/runtime-query-oracle native/RuntimeQueryOracle.c
 * target/runtime-query-oracle
 */
extern int printf(const char *, ...);
void lean_initialize_runtime_module(void);
lean_object *lean_closure_max_args(lean_object *);
lean_object *lean_max_small_nat(lean_object *);
lean_object *lean_libuv_version(lean_object *);
lean_object *lean_openssl_version(lean_object *);
uint8_t lean_internal_has_llvm_backend(lean_object *);
lean_object *lean_internal_get_default_max_memory(void);
lean_object *lean_internal_get_default_max_heartbeat(void);
uint8_t lean_internal_get_default_verbose(lean_object *);
uint32_t lean_internal_get_believer_trust_level(lean_object *);
uint8_t lean_internal_is_multi_thread(lean_object *);
int main(void) {
 lean_initialize_runtime_module();
 lean_object *u=lean_box(0);
 printf("{\"lean_get_max_ctor_fields\":%zu,\"lean_get_max_ctor_scalars_size\":%zu,\"lean_get_max_ctor_tag\":%zu,\"lean_get_usize_size\":%zu,\"lean_closure_max_args\":%zu,\"lean_max_small_nat\":%zu,\"lean_libuv_version\":%zu,\"lean_openssl_version\":%zu,\"lean_internal_has_llvm_backend\":%u,\"lean_internal_get_default_max_memory\":%zu,\"lean_internal_get_default_max_heartbeat\":%zu,\"lean_internal_get_default_verbose\":%u,\"lean_internal_get_believer_trust_level\":%u,\"lean_internal_is_multi_thread\":%u}\n",
   lean_unbox(lean_get_max_ctor_fields(u)),lean_unbox(lean_get_max_ctor_scalars_size(u)),
   lean_unbox(lean_get_max_ctor_tag(u)),lean_unbox(lean_get_usize_size(u)),
   lean_unbox(lean_closure_max_args(u)),lean_unbox(lean_max_small_nat(u)),
   lean_unbox(lean_libuv_version(u)),lean_unbox(lean_openssl_version(u)),
   lean_internal_has_llvm_backend(u),lean_unbox(lean_internal_get_default_max_memory()),
   lean_unbox(lean_internal_get_default_max_heartbeat()),lean_internal_get_default_verbose(u),lean_internal_get_believer_trust_level(u),lean_internal_is_multi_thread(u));
 return 0;
}
