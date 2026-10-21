// Independent tiny API harness. No Lean implementation code is reproduced here.
#include "runtime/init_module.h"
#include "util/init_module.h"
#include "kernel/level.h"
#include <cstdio>
static_assert(sizeof(lean::level) == sizeof(lean_object *));
static_assert(sizeof(lean::name) == sizeof(lean_object *));
int main() {
  lean::initialize_util_module();
  lean::initialize_level();
  {
    using namespace lean;
    level z = mk_level_zero();
    level u = mk_univ_param(name("u"));
    level v = mk_univ_param(name("v"));
    auto result = [](char const *id, level const &lhs, level const &rhs) {
      std::printf("{\"id\":\"%s\",\"operation\":\"lean::is_geq(lhs,rhs)\",\"result\":%s}\n",
                  id, is_geq(lhs,rhs) ? "true" : "false");
    };
    result("succ-imax-u-v_ge_v", mk_succ(mk_imax(u,v)), v);
    result("u-plus-two_ge_one", mk_succ(mk_succ(u)), mk_succ(z));
    result("three_ge_u-plus-one", mk_succ(mk_succ(mk_succ(z))), mk_succ(u));
    result("imax-u-zero_eq_zero_forward",mk_imax(u,z),z);
    result("imax-u-zero_eq_zero_reverse",z,mk_imax(u,z));
  }
  lean::finalize_level();
  lean::finalize_util_module();
}
