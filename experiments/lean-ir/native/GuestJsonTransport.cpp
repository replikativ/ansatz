/* Oracle-only shared producer for a compacted Json DAG. Reuse the pinned,
 * strict generic transport; no native heap scalar extent is guessed. */
#include "ModuleDataTransport.cpp"
extern "C" lean_obj_res l_Int_repr(b_lean_obj_arg);
extern "C" lean_obj_res module_data_transport_mpz_repr(lean_obj_arg value) {
    lean_object *text = l_Int_repr(value);
    lean_dec(value);
    return text;
}
// #eval resolves the private declaration's generated boxed symbol. This thin
// oracle-only adapter has the same borrowed ABI as the Lean external declaration;
// the boxed adapter consumes its retained object argument owners exactly once.
extern "C" LEAN_EXPORT lean_obj_res
l___private_lean_GuestJsonWitnessOracle_0__exportDAG___boxed(
    lean_obj_arg roots, lean_obj_arg metadata, lean_obj_arg path,
    lean_obj_arg verify, lean_obj_arg) {
    lean_object *result = module_data_transport_export(roots, metadata, path, lean_unbox(verify));
    lean_dec(roots); lean_dec(metadata); lean_dec(path);
    return result;
}
