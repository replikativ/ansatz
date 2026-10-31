// Authentic source graph, with typed claims for the pinned Init extension profile.
#include "../native/ModuleDataTransport.cpp"
#include <set>
extern "C" LEAN_EXPORT lean_obj_res matched_init_scalar_census(
    b_lean_obj_arg roots, b_lean_obj_arg names, b_lean_obj_arg literals,
    b_lean_obj_arg irLiterals, b_lean_obj_arg lcnfLiterals, b_lean_obj_arg formats,
    b_lean_obj_arg path) {
    try {
        Graph graph(roots, false);
        std::ofstream out(lean_string_cstr(path), std::ios::binary | std::ios::trunc);
        if (!out) throw TransportError("cannot open scalar census");
        std::set<std::pair<size_t,size_t>> done;
        out << "{\"schema\":\"matched-init-typed-scalars/1\",\"threshold\":2147483647,\"claims\":[";
        bool comma=false;
        auto emit = [&](lean_object *owner, size_t field, char const *sourceType, bool isInt=false) {
            auto found=graph.ids.find(owner);
            if(found==graph.ids.end()) throw TransportError("typed scalar owner not in source graph");
            auto value=lean_ctor_get(owner,field);
            if(!lean_is_scalar(value) || lean_unbox(value)<=2147483647) return;
            if(!done.emplace(found->second,field).second) return;
            if(comma)out<<',';comma=true;
            out << "{\"nodeId\":" << found->second << ",\"fieldIndex\":" << field
                << ",\"value\":\"" << lean_unbox(value) << "\",\"domain\":\"" << (isInt?"Int":"Nat")
                << "\",\"sourceType\":" << quoted(sourceType);
            if(isInt) out << ",\"signedValue\":\"" << lean_scalar_to_int64(value) << '\"';
            out << '}';
        };
        for(size_t i=0;i<lean_array_size(names);++i) emit(lean_array_get_core(names,i),1,"Lean.Name.num");
        for(size_t i=0;i<lean_array_size(literals);++i) emit(lean_array_get_core(literals,i),0,"Lean.Literal.natVal");
        for(size_t i=0;i<lean_array_size(irLiterals);++i) emit(lean_array_get_core(irLiterals,i),0,"Lean.IR.LitVal.num");
        for(size_t i=0;i<lean_array_size(lcnfLiterals);++i) emit(lean_array_get_core(lcnfLiterals,i),0,"Lean.Compiler.LCNF.LitValue.nat");
        for(size_t i=0;i<lean_array_size(formats);++i) {
            auto f=lean_array_get_core(formats,i);
            auto tag=lean_obj_tag(f);
            if(tag==4) emit(f,0,"Std.Format.nest",true);
            else if(tag==7) emit(f,0,"Std.Format.tag");
            else throw TransportError("typed Format claim has wrong constructor");
        }
        size_t persistent=0, singleThreaded=0, multiThreaded=0;
        std::vector<std::pair<size_t,int>> counted;
        for(size_t id=0;id<graph.objects.size();++id) {
            auto object=graph.objects[id];
            int rc=lean_internal_get_rc(object);
            if(rc==0) ++persistent;
            else { if(rc>0) ++singleThreaded; else ++multiThreaded; counted.emplace_back(id,rc); }
        }
        out << "],\"claimCount\":" << done.size() << ",\"graphNodes\":" << graph.objects.size()
            << ",\"sourceLifetime\":{\"persistent\":" << persistent
            << ",\"singleThreaded\":" << singleThreaded << ",\"multiThreaded\":" << multiThreaded
            << ",\"nonPersistent\":[";
        bool first=true;
        for(auto [id,rc]:counted) { if(!first)out<<',';first=false;out<<"{\"nodeId\":"<<id<<",\"rc\":"<<rc<<'}'; }
        out << "]}}\n";
        out.close(); if(!out)throw TransportError("failed writing scalar census");
        return lean_io_result_mk_ok(lean_box(0));
    } catch(TransportError const &e) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(e.message.c_str())));
    }
}
