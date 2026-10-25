/* Pinned Lean 4.33.1 ModuleData object-DAG producer, native-only.
 * Generic immediate words are NOT interpreted as Nat/Int. Constructor scalar
 * tails include the compacted allocation padding, whose semantic types cannot
 * be recovered from a Lean object header. No native addresses are emitted.
 * See pinned compact.cpp insert_constructor/array/sarray/string/mpz and
 * lean_object_byte_size: m_cs_sz stores compacted small-object allocation size.
 */
#include <lean/lean.h>
#include <fstream>
#include <iomanip>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
#include <deque>
#include <cstring>
#include <cstdio>
#include <execinfo.h>
#include <signal.h>
#include <unistd.h>

extern "C" lean_obj_res module_data_transport_mpz_repr(lean_obj_arg);
// Public Float.ofBits canonicalizes NaNs; this native-only canary deliberately
// constructs an opaque payload without numeric conversion/canonicalization.
extern "C" LEAN_EXPORT double module_data_transport_raw_nan(lean_obj_arg) {
    uint64_t bits=UINT64_C(0x7ff8000000000001);double value;
    std::memcpy(&value,&bits,sizeof(value));return value;
}

namespace {
void crash_trace(int sig) {
    void *frames[48]; int n=::backtrace(frames,48); ::backtrace_symbols_fd(frames,n,2); _exit(128+sig);
}
__attribute__((constructor)) void install_trace() {
    if(std::getenv("MODULE_DATA_TRANSPORT_TRACE")) ::signal(SIGSEGV,crash_trace);
}

constexpr size_t MAX_NODES = 25000000;
constexpr size_t MAX_BYTES = size_t(2) << 30;
struct TransportError { std::string message; explicit TransportError(std::string value):message(std::move(value)){} };
struct Edge {
    bool immediate;
    size_t value;
    bool operator==(Edge const &b) const { return immediate == b.immediate && value == b.value; }
};
struct Node {
    lean_object *source = nullptr;
    unsigned tag = 0, other = 0;
    size_t bytes = 0, size = 0, capacity = 0, length = 0;
    std::vector<Edge> refs;
    std::string data;
    bool operator==(Node const &b) const {
        return tag == b.tag && other == b.other && bytes == b.bytes && size == b.size &&
          capacity == b.capacity && length == b.length && refs == b.refs && data == b.data;
    }
};
std::string hex(std::string const &data) {
    static char const digits[] = "0123456789abcdef";
    std::string result; result.reserve(data.size()*2);
    for (unsigned char byte : data) { result += digits[byte>>4]; result += digits[byte&15]; }
    return result;
}
std::string quoted(std::string const &text) {
    std::ostringstream out; out << '"';
    for (unsigned char c : text) {
        if (c == '"' || c == '\\') out << '\\' << c;
        else if (c < 32) out << "\\u00" << "0123456789abcdef"[c>>4] << "0123456789abcdef"[c&15];
        else out << c;
    }
    out << '"'; return out.str();
}
void edge(std::ostream &out, Edge e) {
    if (e.immediate) out << "{\"immediate\":\"" << e.value << "\"}";
    else out << "{\"ref\":" << e.value << '}';
}
void write_node(std::ostream &,size_t,Node const &);
struct Graph {
    std::unordered_map<lean_object*,size_t> ids;
    std::vector<lean_object*> objects;
    std::deque<Node> nodes;
    std::map<unsigned,size_t> tags;
    std::map<std::tuple<unsigned,size_t,size_t>,size_t> layouts;
    Edge root;
    size_t total_bytes = 0, references = 0, immediates = 0;
    Edge intern(lean_object *p) {
        if (!p) throw TransportError("null pointer in ModuleData graph");
        if (lean_is_scalar(p)) { ++immediates; return {true,lean_unbox(p)}; }
        ++references;
        auto found = ids.find(p);
        if (found != ids.end()) return {false,found->second};
        if (objects.size() >= MAX_NODES) throw TransportError("ModuleData node limit exceeded");
        size_t id = objects.size(); ids.emplace(p,id); objects.push_back(p);
        return {false,id};
    }
    explicit Graph(lean_object *p,bool retain=true,std::ostream *sink=nullptr) {
        root = intern(p);
        for (size_t i = 0; i < objects.size(); ++i) {
            // Full imports stream snapshots; only IDs and source pointers stay
            // live. Small native clone oracles explicitly retain Node payloads.
            Node n; auto p = objects[i]; n.source = p;
            n.tag = lean_ptr_tag(p); n.other = lean_ptr_other(p);
            if (n.tag <= LeanMaxCtorTag) {
                // Heap constructor headers do not expose the initialized scalar
                // extent. Reading allocator padding is unsafe; only compacted
                // constructors carry an exact, fully mapped byte extent here.
                if (lean_has_rc(p) || p->m_cs_sz == 0)
                    throw TransportError("heap constructor has unknown initialized scalar extent");
                n.bytes = lean_object_byte_size(p);
                size_t prefix = sizeof(lean_object) + size_t(n.other)*sizeof(void*);
                if (n.bytes < prefix || n.bytes-prefix > LEAN_MAX_CTOR_SCALARS_SIZE)
                    throw TransportError("invalid compacted constructor allocation size");
                for (unsigned j = 0; j < n.other; ++j) n.refs.push_back(intern(lean_ctor_get(p,j)));
                n.data.assign(reinterpret_cast<char*>(lean_ctor_scalar_cptr(p)),n.bytes-prefix);
            } else if (n.tag == LeanArray) {
                n.size = lean_array_size(p); n.capacity = lean_array_capacity(p);
                if (n.size > n.capacity || n.capacity > MAX_BYTES/sizeof(void*))
                    throw TransportError("invalid array size/capacity");
                n.bytes = sizeof(lean_array_object)+n.capacity*sizeof(void*);
                for (size_t j = 0; j < n.size; ++j) n.refs.push_back(intern(lean_array_get_core(p,j)));
            } else if (n.tag == LeanScalarArray) {
                n.size = lean_sarray_size(p); n.capacity = lean_sarray_capacity(p);
                if (!n.other || n.size > n.capacity || n.capacity > MAX_BYTES/n.other)
                    throw TransportError("invalid scalar-array element width/size");
                n.bytes = sizeof(lean_sarray_object)+n.capacity*n.other;
                n.data.assign(reinterpret_cast<char*>(lean_sarray_cptr(p)),n.size*n.other);
            } else if (n.tag == LeanString) {
                auto s = lean_to_string(p); n.size = s->m_size; n.capacity = s->m_capacity; n.length = s->m_length;
                if (!n.size || n.size > n.capacity || n.capacity > MAX_BYTES || s->m_data[n.size-1] != 0)
                    throw TransportError("invalid Lean string layout");
                n.bytes = sizeof(lean_string_object)+n.capacity;
                n.data.assign(s->m_data,n.size);
            } else if (n.tag == LeanMPZ) {
                lean_inc(p); // exported Lean helper consumes this temporary owner
                auto s = module_data_transport_mpz_repr(p);
                n.data.assign(lean_string_cstr(s),lean_string_size(s)-1); lean_dec(s);
                n.bytes = 0; // Limb count/allocation are deliberately not a portable MPZ representation.
            } else {
                throw TransportError("unsupported native tag " + std::to_string(n.tag) +
                    " at object " + std::to_string(i) + "; closures, externals and native execution objects are not portable");
            }
            if (n.bytes > MAX_BYTES-total_bytes) throw TransportError("ModuleData byte limit exceeded");
            total_bytes += n.bytes;
            ++tags[n.tag];
            if(n.tag<=LeanMaxCtorTag)++layouts[{n.tag,n.refs.size(),n.data.size()}];
            if(sink)write_node(*sink,i,n);
            if(retain)nodes.push_back(std::move(n));
        }
    }
};

// The native roundtrip reconstructs the captured graph without re-reading any
// original pointers. Clones are intentionally process-lifetime probe allocations:
// no destructor runs on the graph with mixed compacted/persistent headers. This
// is a native validation executable, not the production guest heap importer.
// Constructor non-heap headers preserve the known scalar byte extent.
bool verify(Graph const &source) {
    std::vector<lean_object*> copy(source.nodes.size(),nullptr);
    for (size_t i = 0; i < copy.size(); ++i) {
        auto const &n = source.nodes[i]; lean_object *p;
        if (n.tag <= LeanMaxCtorTag) {
            p = lean_alloc_ctor_memory(n.bytes);
            lean_set_non_heap_header(p,n.bytes,n.tag,n.other);
            std::memset(lean_ctor_obj_cptr(p),0,n.bytes-sizeof(lean_object));
            std::memcpy(lean_ctor_scalar_cptr(p),n.data.data(),n.data.size());
        } else if (n.tag == LeanArray) p = lean_alloc_array(n.size,n.capacity);
        else if (n.tag == LeanScalarArray) {
            p = lean_alloc_sarray(n.other,n.size,n.capacity);
            std::memcpy(lean_sarray_cptr(p),n.data.data(),n.data.size());
        } else if (n.tag == LeanString) {
            auto s = reinterpret_cast<lean_string_object*>(lean_alloc_object(sizeof(lean_string_object)+n.capacity));
            lean_set_st_header(reinterpret_cast<lean_object*>(s),LeanString,0);
            s->m_size=n.size; s->m_capacity=n.capacity; s->m_length=n.length;
            std::memcpy(s->m_data,n.data.data(),n.data.size()); p=reinterpret_cast<lean_object*>(s);
        } else {
            p = lean_cstr_to_int(n.data.c_str());
            if (lean_is_scalar(p)) p = lean_big_int_to_int(lean_scalar_to_int(p));
        }
        copy[i] = p;
    }
    auto resolve = [&](Edge e) { return e.immediate ? lean_box(e.value) : copy.at(e.value); };
    for (size_t i=0;i<copy.size();++i) {
        auto const &n=source.nodes[i]; auto p=copy[i];
        for (size_t j=0;j<n.refs.size();++j) {
            auto child=resolve(n.refs[j]);
            if (n.tag == LeanArray) lean_array_set_core(p,j,child);
            else lean_ctor_set(p,j,child);
        }
    }
    Graph restored(resolve(source.root));
    return source.root==restored.root && source.nodes==restored.nodes;
}
void write_node(std::ostream &out,size_t id,Node const &n) {
    out << "{\"id\":" << id << ",\"tag\":" << n.tag << ",\"objectBytes\":" << n.bytes;
    if (n.tag <= LeanMaxCtorTag) out << ",\"kind\":\"ctor\",\"scalarBytesIncludePadding\":true";
    else if (n.tag==LeanArray) out << ",\"kind\":\"array\"";
    else if (n.tag==LeanScalarArray) out << ",\"kind\":\"scalar-array\",\"elementBytes\":" << n.other;
    else if (n.tag==LeanString) out << ",\"kind\":\"string\",\"utf8Length\":" << n.length;
    else out << ",\"kind\":\"mpz\",\"signedDecimal\":" << quoted(n.data);
    if (n.tag==LeanArray || n.tag==LeanScalarArray || n.tag==LeanString)
        out << ",\"size\":" << n.size << ",\"capacity\":" << n.capacity;
    out << ",\"fields\": [";
    for (size_t i=0;i<n.refs.size();++i) { if(i)out<<','; edge(out,n.refs[i]); }
    out << ']';
    if (n.tag!=LeanMPZ) out << ",\"bytesHex\":" << quoted(hex(n.data));
    out << "}\n";
}
std::string summary(Graph const &graph,bool verified) {
    auto const &tags=graph.tags;
    auto const &layouts=graph.layouts;
    std::ostringstream out;
    out << "{\"nodes\":" << graph.objects.size() << ",\"sourceAllocationBytes\":" << graph.total_bytes
        << ",\"referenceOccurrences\":" << graph.references << ",\"immediateOccurrences\":" << graph.immediates
        << ",\"sharingRevisits\":" << graph.references-graph.objects.size()
        << ",\"nativeRoundtripVerified\":" << (verified?"true":"false") << ",\"tags\":{";
    bool comma=false;
    for(auto [tag,count]:tags) {if(comma)out<<',';comma=true;out<<quoted(std::to_string(tag))<<':'<<count;}
    out<<"},\"constructorLayouts\":[";comma=false;
    for(auto const &entry:layouts) {
        if(comma)out<<',';comma=true;
        out<<"{\"tag\":"<<std::get<0>(entry.first)<<",\"objectFields\":"<<std::get<1>(entry.first)
           <<",\"scalarBytesWithPadding\":"<<std::get<2>(entry.first)<<",\"count\":"<<entry.second<<'}';
    }
    out<<"]}";return out.str();
}
}
extern "C" LEAN_EXPORT lean_obj_res module_data_transport_export(
    b_lean_obj_arg roots,b_lean_obj_arg metadata,b_lean_obj_arg path,uint8_t check) {
    std::string temporary, spool;
    try {
        uint16_t endian=1;
        if(sizeof(void*)!=8 || *reinterpret_cast<unsigned char*>(&endian)!=1)
            throw TransportError("ModuleDataTransport requires pinned little-endian x86-64");
        std::string filename(lean_string_cstr(path),lean_string_size(path)-1);
        if(filename.find('\0')!=std::string::npos)throw TransportError("NUL in transport path");
        temporary=filename+".partial";
        spool=filename+".objects.partial";
        std::ofstream body;
        if(!check) {
            body.open(spool,std::ios::binary|std::ios::trunc);
            if(!body)throw TransportError("cannot open streamed ModuleData body");
        }
        Graph graph(roots,check,check?nullptr:&body);
        if(!check) {body.close();if(!body)throw TransportError("failed writing streamed ModuleData body");}
        bool verified=check && verify(graph);
        if(check && !verified)throw TransportError("native ModuleData graph roundtrip mismatch");
        auto info=summary(graph,verified);
        std::ofstream out(temporary,std::ios::binary|std::ios::trunc);
        if(!out)throw TransportError("cannot open transport output");
        out<<"{\"kind\":\"manifest\",\"schema\":\"lean-module-dag/1\",\"wordBits\":64,\"byteOrder\":\"little\","
              "\"immediateEncoding\":\"unsigned-native-tagged-payload\",\"root\":";
        edge(out,graph.root);
        out<<",\"input\":"<<lean_string_cstr(metadata)<<",\"inventory\":"<<info<<"}\n";
        if(check)for(size_t i=0;i<graph.nodes.size();++i)write_node(out,i,graph.nodes[i]);
        else {std::ifstream bodyIn(spool,std::ios::binary);out<<bodyIn.rdbuf();if(!bodyIn)throw TransportError("cannot read streamed ModuleData body");}
        out.close();if(!out)throw TransportError("failed writing transport output");
        if(std::rename(temporary.c_str(),filename.c_str())!=0)throw TransportError("cannot publish transport output");
        if(!spool.empty())std::remove(spool.c_str());
        return lean_io_result_mk_ok(lean_mk_string(info.c_str()));
    } catch(TransportError const &error) {
        if(!temporary.empty())std::remove(temporary.c_str());
        if(!spool.empty())std::remove(spool.c_str());
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(error.message.c_str())));
    }
}
