#include <lean/lean.h>
extern int printf(const char *, ...);
/* Pinned 4.33.1 runtime heartbeat ABI/counter oracle.
 * leanc +leanprover/lean4:v4.33.1 -o target/runtime-heartbeat-oracle native/RuntimeHeartbeatOracle.c
 * target/runtime-heartbeat-oracle
 * Getter/reset operate on allocator thread-local UInt64, not kernel heartbeat
 * budgets. Logical hosted heap allocation charges intentionally differ from
 * native small-object allocation counts.
 */
void lean_initialize_runtime_module(void);
lean_object *lean_io_get_num_heartbeats(void);
lean_object *lean_io_set_heartbeats(lean_object *);
static uint64_t read_count(void) {
  lean_object *n = lean_io_get_num_heartbeats();
  uint64_t count = lean_uint64_of_nat(n);
  lean_dec(n);
  return count;
}
int main(void) {
  lean_initialize_runtime_module();
  lean_dec(lean_io_set_heartbeats(lean_box(7)));
  uint64_t initial = read_count();
  lean_object *ctor = lean_alloc_ctor(0, 0, 0);
  uint64_t after_ctor = read_count();
  lean_dec(ctor);
  lean_object *large = lean_cstr_to_nat("18446744073709551621");
  lean_inc(large);
  lean_dec(lean_io_set_heartbeats(large));
  unsigned owner_count = lean_is_scalar(large) ? 0 : lean_is_exclusive(large);
  uint64_t truncated = read_count();
  lean_dec(large);
  lean_object *max = lean_cstr_to_nat("18446744073709551615");
  lean_dec(lean_io_set_heartbeats(max));
  ctor = lean_alloc_ctor(0, 0, 0);
  uint64_t wrapped = read_count();
  lean_dec(ctor);
  printf("{\"reset\":%llu,\"after_ctor\":%llu,\"mpz_mod64\":%llu,\"remaining_mpz_owner_exclusive\":%u,\"wrap_after_ctor\":%llu}\n",
    (unsigned long long)initial, (unsigned long long)after_ctor,
    (unsigned long long)truncated, owner_count, (unsigned long long)wrapped);
  return !(initial == 7 && after_ctor == 8 && truncated == 5 && owner_count == 1 && wrapped == 0);
}
