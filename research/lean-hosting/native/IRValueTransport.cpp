/* Oracle-only strict native compacted IR.Decl DAG exporter. */
#include "GuestJsonTransport.cpp"
extern "C" LEAN_EXPORT lean_obj_res
l___private_lean_IRValueWitnessOracle_0__exportDAG___boxed(
    lean_obj_arg roots, lean_obj_arg metadata, lean_obj_arg path,
    lean_obj_arg verify, lean_obj_arg) {
    lean_object *result = module_data_transport_export(roots, metadata, path, lean_unbox(verify));
    lean_dec(roots); lean_dec(metadata); lean_dec(path);
    return result;
}
