// Reuse the authentic graph algorithm unchanged; this translation unit adds only
// source-typed scalar-use claims keyed by that graph's actual object IDs.
#include "../native/ModuleDataTransport.cpp"
#include <set>
#include <limits>
extern "C" LEAN_EXPORT lean_obj_res matched_prelude_scalar_census(
    b_lean_obj_arg roots, b_lean_obj_arg names, b_lean_obj_arg literals, b_lean_obj_arg irLiterals, b_lean_obj_arg path) {
    try {
        Graph graph(roots, false);
        std::ofstream out(lean_string_cstr(path), std::ios::binary | std::ios::trunc);
        if (!out) throw TransportError("cannot open scalar census");
        std::set<std::pair<size_t,size_t>> done;
        out << "{\"schema\":\"matched-prelude-typed-scalars/1\",\"threshold\":2147483647,\"claims\":[";
        bool comma=false;
        auto emit = [&](lean_object *owner, size_t field, char const *sourceType) {
            auto found=graph.ids.find(owner);
            if(found==graph.ids.end()) throw TransportError("typed scalar owner not in source graph");
            auto value=lean_ctor_get(owner,field);
            if(!lean_is_scalar(value) || lean_unbox(value)<=2147483647) return;
            if(!done.emplace(found->second,field).second) return;
            if(comma)out<<',';comma=true;
            out << "{\"nodeId\":" << found->second << ",\"fieldIndex\":" << field
                << ",\"value\":\"" << lean_unbox(value) << "\",\"domain\":\"Nat\",\"sourceType\":"
                << quoted(sourceType) << '}';
        };
        for(size_t i=0;i<lean_array_size(names);++i) emit(lean_array_get_core(names,i),1,"Lean.Name.num");
        for(size_t i=0;i<lean_array_size(literals);++i) emit(lean_array_get_core(literals,i),0,"Lean.Literal.natVal");
        for(size_t i=0;i<lean_array_size(irLiterals);++i) emit(lean_array_get_core(irLiterals,i),0,"Lean.IR.LitVal.num");
        out << "],\"claimCount\":" << done.size() << ",\"graphNodes\":" << graph.objects.size() << "}\n";
        out.close(); if(!out)throw TransportError("failed writing scalar census");
        return lean_io_result_mk_ok(lean_box(0));
    } catch(TransportError const &e) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(e.message.c_str())));
    }
}
