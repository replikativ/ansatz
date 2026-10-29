#include <lean/lean.h>

namespace lean { void reset_heartbeat(); }

// Kernel check heartbeats differ from IO's allocation heartbeat counter.
extern "C" LEAN_EXPORT lean_object * ansatz111_reset_kernel_hb() {
    lean::reset_heartbeat();
    return lean_io_result_mk_ok(lean_box(0));
}
