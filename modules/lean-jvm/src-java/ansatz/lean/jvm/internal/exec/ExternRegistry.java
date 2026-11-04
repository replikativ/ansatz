package ansatz.lean.jvm.internal.exec;

import java.util.*;
import static ansatz.lean.jvm.internal.exec.Interpreter.*;

/** Supported Lean runtime extern table. Maps each captured extern symbol and its exact
 * ABI (parameter types, borrow flags, result type) to an intrinsic id. */
final class ExternRegistry {
    private ExternRegistry() {
    }

    /** Exact captured ABI, deliberately distinct from physical JVM lanes. */
    static final class ExternSpec {
        final String symbol,resultType;
        final int intrinsic;
        final String[] paramTypes;
        final boolean[] borrowed;
        ExternSpec(String symbol,int intrinsic,String resultType,String[] paramTypes,boolean[] borrowed) {
            this.symbol=symbol; this.intrinsic=intrinsic; this.resultType=resultType;
            this.paramTypes=paramTypes.clone(); this.borrowed=borrowed.clone();
            if(paramTypes.length!=borrowed.length) throw new IllegalArgumentException("Invalid extern registry entry");
        }
        boolean matches(Map<String,Object> declaration) {
            List<Object> params=list(declaration.get("xs"));
            if(!resultType.equals(declaration.get("type"))||params.size()!=paramTypes.length) return false;
            for(int i=0;i<params.size();i++) {
                Map<String,Object> p=map(params.get(i));
                if(!paramTypes[i].equals(p.get("ty"))||!Boolean.valueOf(borrowed[i]).equals(p.get("borrow"))) return false;
            }
            return true;
        }
    }
    static Map<String,List<ExternSpec>> externRegistry() {
        Map<String,List<ExternSpec>> registry=new LinkedHashMap<>();
        String[] symbols={"lean_nat_add","lean_nat_sub","lean_nat_mod","lean_nat_dec_eq","lean_nat_dec_lt",
                          "lean_nat_mul","lean_nat_div","lean_nat_pow"};
        int[] ops={ADD,SUB,MOD,EQ,LT,MUL,DIV,POW};
        for(int i=0;i<symbols.length;i++) register(registry,new ExternSpec(symbols[i],ops[i],
                ops[i]==EQ||ops[i]==LT?"uint8":"tobject",new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_usize_of_nat",USIZE_NAT,"usize",new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_usize_of_nat",USIZE_NAT,"usize",new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_string_of_usize",USIZE_REPR,"object",new String[]{"usize"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint32_to_nat",U32_NAT,"tobject",new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_dec_eq",U32_EQ,"uint8",new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint32_dec_le",U32_LE,"uint8",new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_system_platform_nbits",PLATFORM_BITS,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_max_ctor_fields",LAYOUT_FIELDS,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_max_ctor_scalars_size",LAYOUT_SCALARS,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_max_ctor_tag",LAYOUT_TAG,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_usize_size",LAYOUT_USIZE,"tobject",new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_dec_lt",U32_LT,"uint8",new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_to_nat",U64_TO_NAT,"tobject",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint16_dec_eq",U16_EQ,"uint8",new String[]{"uint16","uint16"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint16_to_nat",U16_NAT,"tagged",new String[]{"uint16"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_push",STR_PUSH,"object",new String[]{"object","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_mk",STR_LIST,"object",new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_any",STR_ANY,"uint8",new String[]{"object","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_io_metadata",FS_METADATA,"object",new String[]{"object","void"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_mk",FS_OPEN,"object",new String[]{"object","uint8","void"},new boolean[]{true,false,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_read",FS_READ,"object",new String[]{"tobject","usize","void"},new boolean[]{true,false,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_get_line",FS_LINE,"object",new String[]{"tobject","void"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_write",FS_WRITE,"object",new String[]{"tobject","object","void"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_put_str",FS_PUT,"object",new String[]{"tobject","object","void"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_flush",FS_FLUSH,"object",new String[]{"tobject","void"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_rewind",FS_REWIND,"object",new String[]{"tobject","void"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_truncate",FS_TRUNCATE,"object",new String[]{"tobject","void"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_io_prim_handle_is_tty",FS_TTY,"uint8",new String[]{"tobject","void"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_string_isprefixof",STR_IS_PREFIX,"uint8",new String[]{"object","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_utf8_get_fast",STR_GET,"uint32",new String[]{"object","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_string_utf8_next_fast",STR_NEXT,"tagged",new String[]{"object","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_string_append",STR_APPEND,"object",new String[]{"object","object"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_string_utf8_byte_size",STR_SIZE,"tagged",new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_array_mk",ARRAY_MK,"object",new String[]{"erased","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_array_get_size",ARRAY_SIZE,"tagged",new String[]{"erased","object"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_array_fget_borrowed",ARRAY_GET,"tobject",new String[]{"erased","object","tobject","erased"},new boolean[]{false,true,true,false}));
        register(registry,new ExternSpec("lean_get_stdout",GET_STDOUT,"object",new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_dbg_trace_if_shared",DBG_TRACE_SHARED,"tobject",
                new String[]{"erased","object","tobject"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_get_stdin",GET_STDIN,"object",new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_stderr",GET_STDERR,"object",new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_get_set_stdin",SET_STDIN,"object",new String[]{"object","void"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_get_set_stdout",SET_STDOUT,"object",new String[]{"object","void"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_get_set_stderr",SET_STDERR,"object",new String[]{"object","void"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_panic_fn_borrowed",PANIC,"tobject",new String[]{"erased","tobject","object"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_st_mk_ref",REF_MK,"tobject",
                new String[]{"erased","erased","tobject","void"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_st_ref_get",REF_GET,"tobject",
                new String[]{"erased","erased","tobject","void"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_st_ref_set",REF_SET,"tagged",
                new String[]{"erased","erased","tobject","tobject","void"},new boolean[]{false,false,true,false,false}));
        register(registry,new ExternSpec("lean_st_ref_swap",REF_SWAP,"tobject",
                new String[]{"erased","erased","tobject","tobject","void"},new boolean[]{false,false,true,false,false}));
        register(registry,new ExternSpec("lean_st_ref_take",REF_TAKE,"tobject",
                new String[]{"erased","erased","tobject","void"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_st_ref_ptr_eq",REF_PTR_EQ,"uint8",
                new String[]{"erased","erased","tobject","tobject","void"},new boolean[]{false,false,true,true,false}));
        register(registry,new ExternSpec("lean_mk_empty_array_with_capacity",ARRAY_EMPTY,"object",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_array_push",ARRAY_PUSH,"object",
                new String[]{"erased","object","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_array_pop",ARRAY_POP,"object",
                new String[]{"erased","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_array_size",ARRAY_USIZE,"usize",
                new String[]{"erased","object"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_array_fget",ARRAY_FGET,"tobject",
                new String[]{"erased","object","tobject","erased"},new boolean[]{false,true,true,false}));
        register(registry,new ExternSpec("lean_array_uget",ARRAY_UGET,"tobject",
                new String[]{"erased","object","usize","erased"},new boolean[]{false,true,false,false}));
        register(registry,new ExternSpec("lean_array_uget_borrowed",ARRAY_UGET_BORROWED,"tobject",
                new String[]{"erased","object","usize","erased"},new boolean[]{false,true,false,false}));
        register(registry,new ExternSpec("lean_array_fset",ARRAY_FSET,"object",
                new String[]{"erased","object","tobject","tobject","erased"},new boolean[]{false,false,true,false,false}));
        register(registry,new ExternSpec("lean_array_set",ARRAY_CHECKED_SET,"object",
                new String[]{"erased","object","tobject","tobject"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_array_uset",ARRAY_USET,"object",
                new String[]{"erased","object","usize","tobject","erased"},new boolean[]{false,false,false,false,false}));
        register(registry,new ExternSpec("lean_array_fswap",ARRAY_SWAP,"object",
                new String[]{"erased","object","tobject","tobject","erased","erased"},new boolean[]{false,false,true,true,false,false}));
        register(registry,new ExternSpec("lean_array_to_list",ARRAY_LIST,"tobject",
                new String[]{"erased","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_mk_array",ARRAY_REPLICATE,"object",
                new String[]{"erased","tobject","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_string_utf8_at_end",STR_END,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_get",STR_SAFE_GET,"uint32",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_next",STR_SAFE_NEXT,"tobject",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_prev",STR_PREV,"tobject",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_is_valid_pos",STR_VALID,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_utf8_extract",STR_EXTRACT,"object",
                new String[]{"object","tobject","tobject"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_string_dec_eq",STR_EQ,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_dec_lt",STR_LT,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_compare",STR_COMPARE,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_string_get_byte_fast",STR_BYTE,"uint8",
                new String[]{"object","tobject","erased"},new boolean[]{true,false,false}));
        register(registry,new ExternSpec("lean_string_contains",STR_CONTAINS,"uint8",
                new String[]{"object","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_length",STR_LENGTH,"tobject",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_string_length",STR_LENGTH,"tagged",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_string_utf8_set",STR_SET,"object",
                new String[]{"object","tobject","uint32"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_string_utf8_set",STR_POS_SET,"object",
                new String[]{"object","tobject","uint32","erased"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_nat_dec_le",NAT_LE,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_log2",NAT_LOG2,"tobject",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_nat_lor",NAT_OR,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_shiftl",NAT_SHL,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_shiftr",NAT_SHR,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_task_map",TASK_MAP,"object",
                new String[]{"erased","erased","tobject","object","tobject","uint8"},
                new boolean[]{false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_task_pure",TASK_PURE,"object",
                new String[]{"erased","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_task_get_own",TASK_GET,"tobject",
                new String[]{"erased","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_io_promise_new",PROMISE_NEW,"tobject",
                new String[]{"erased","erased","void"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_io_promise_resolve",PROMISE_RESOLVE,"tagged",
                new String[]{"erased","tobject","tobject","void"},new boolean[]{false,false,true,false}));
        register(registry,new ExternSpec("lean_io_promise_result_opt",PROMISE_RESULT,"object",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_task_bind",TASK_BIND,"object",
                new String[]{"erased","erased","object","object","tobject","uint8"},new boolean[]{false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_io_map_task",IO_TASK_MAP,"object",
                new String[]{"erased","erased","object","object","tobject","uint8","void"},new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_io_bind_task",IO_TASK_BIND,"object",
                new String[]{"erased","erased","object","object","tobject","uint8","void"},new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_io_get_task_state",TASK_STATE,"uint8",
                new String[]{"erased","object","void"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_io_wait",TASK_WAIT,"tobject",
                new String[]{"erased","object","void"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_io_cancel",TASK_CANCEL,"tagged",
                new String[]{"erased","object","void"},new boolean[]{false,true,false}));
        register(registry,new ExternSpec("lean_io_check_canceled",TASK_CANCELED,"uint8",
                new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_option_get_or_block",OPTION_BLOCK,"tobject",
                new String[]{"erased","erased","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_task_spawn",TASK_SPAWN,"object",
                new String[]{"erased","tobject","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_io_as_task",IO_AS_TASK,"object",
                new String[]{"erased","object","tobject","void"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_array_get",ARRAY_CHECKED_GET,"tobject",
                new String[]{"erased","tobject","object","tobject"},new boolean[]{false,true,true,true}));
        register(registry,new ExternSpec("lean_array_get_borrowed",ARRAY_CHECKED_BORROWED,"tobject",
                new String[]{"erased","tobject","object","tobject"},new boolean[]{false,true,true,true}));
        register(registry,new ExternSpec("lean_io_initializing",IO_INITIALIZING,"uint8",
                new String[]{"void"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_usize_dec_lt",USIZE_LT,"uint8",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_add",USIZE_ADD,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_dec_eq",USIZE_EQ,"uint8",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_sub",USIZE_SUB,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_to_nat",USIZE_TO_NAT,"tobject",
                new String[]{"usize"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_usize_shift_right",USIZE_SHR,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_shift_left",USIZE_SHL,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_land",USIZE_AND,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint8_to_nat",U8_NAT,"tagged",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint8_of_nat",U8_FROM_NAT,"uint8",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint8_of_nat",U8_FROM_NAT,"uint8",
                new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_uint8_of_nat_mk",U8_OWNED_NAT,"uint8",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint16_of_nat",U16_FROM_NAT,"uint16",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint16_of_nat",U16_FROM_NAT,"uint16",
                new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_uint16_of_nat_mk",U16_OWNED_NAT,"uint16",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint8_dec_eq",U8_EQ,"uint8",
                new String[]{"uint8","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint8_land",U8_AND,"uint8",
                new String[]{"uint8","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint8_dec_le",U8_LE,"uint8",
                new String[]{"uint8","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint32_of_nat",U32_FROM_NAT,"uint32",
                new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_uint32_of_nat",U32_FROM_NAT,"uint32",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint32_to_uint8",U32_TO_U8,"uint8",
                new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_add",U32_ADD,"uint32",
                new String[]{"uint32","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_dec_le",USIZE_LE,"uint8",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_usize_mul",USIZE_MUL,"usize",
                new String[]{"usize","usize"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_hash",STR_HASH,"uint64",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_runtime_mark_persistent",MARK_PERSISTENT,"tobject",
                new String[]{"erased","tobject","void"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_profileit",PROFILE_IT,"tobject",
                new String[]{"erased","object","object","tobject","tobject"},new boolean[]{false,true,true,false,false}));
        register(registry,new ExternSpec("lean_instantiate_level_mvars",LEVEL_INSTANTIATE,"object",
                new String[]{"object","tobject"},new boolean[]{false,false}));
        if(EXPR_INSTANTIATION_NATIVE_READY) register(registry,new ExternSpec("lean_instantiate_expr_mvars",EXPR_INSTANTIATE_MVARS,"object",
                new String[]{"object","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_void_mk",VOID_MK,"void",
                new String[]{"erased","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_find_ext_expr",EXPR_FIND_EXT,"tobject",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_sharecommon_quick",SHARECOMMON_QUICK,"tobject",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_expr_instantiate",EXPR_INSTANTIATE,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate1",EXPR_INSTANTIATE1,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate_range",EXPR_INSTANTIATE_RANGE,"object",
                new String[]{"object","tobject","tobject","object"},new boolean[]{true,true,true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate_rev",EXPR_INSTANTIATE_REV,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_instantiate_rev_range",EXPR_INSTANTIATE_REV_RANGE,"object",
                new String[]{"object","tobject","tobject","object"},new boolean[]{true,true,true,true}));
        register(registry,new ExternSpec("lean_expr_lift_loose_bvars",EXPR_LIFT,"object",
                new String[]{"object","tobject","tobject"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_replace_expr",EXPR_REPLACE,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_abstract_range",EXPR_ABSTRACT_RANGE,"object",
                new String[]{"object","tobject","object"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_expr_abstract",EXPR_ABSTRACT,"object",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_find_expr",EXPR_FIND,"tobject",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_eqv",EXPR_EQV,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_level_eq",LEVEL_EQUAL,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_equal",EXPR_EQUAL,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_quick_lt",EXPR_QUICK_LT,"uint8",
                new String[]{"object","object"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_has_loose_bvar",EXPR_HAS_LOOSE,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_expr_lower_loose_bvars",EXPR_LOWER,"object",
                new String[]{"object","tobject","tobject"},new boolean[]{true,true,true}));
        register(registry,new ExternSpec("lean_expr_data",EXPR_CACHE,"uint64",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_expr_mk_data",EXPR_DATA,"uint64",
                new String[]{"uint64","tobject","uint32","uint8","uint8","uint8","uint8"},
                new boolean[]{false,false,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_expr_mk_app_data",EXPR_APP_DATA,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_level_mk_data",LEVEL_DATA,"uint64",
                new String[]{"uint64","tobject","uint8","uint8"},new boolean[]{false,false,false,false}));
        register(registry,new ExternSpec("lean_uint8_to_uint32",U8_TO_U32,"uint32",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_to_uint8",U64_TO_U8,"uint8",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint8_to_uint64",U8_TO_U64,"uint64",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_to_uint64",U32_TO_U64,"uint64",
                new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_usize_to_uint64",USIZE_TO_U64,"uint64",
                new String[]{"usize"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_bool_to_uint64",BOOL_U64,"uint64",
                new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_add",U64_ADD,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_sub",U64_SUB,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_mul",U64_MUL,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_div",U64_DIV,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_mod",U64_MOD,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_land",U64_AND,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_lor",U64_OR,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_complement",U64_NOT,"uint64",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_neg",U64_NEG,"uint64",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_log2",U64_LOG2,"uint64",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_shift_left",U64_SHL,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_dec_le",U64_LE,"uint8",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_mix_hash",U64_MIX,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_of_nat",U64_NAT,"uint64",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_uint64_of_nat",U64_NAT,"uint64",
                new String[]{"tobject","erased"},new boolean[]{true,false}));
        register(registry,new ExternSpec("lean_uint64_shift_right",U64_SHR,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_xor",U64_XOR,"uint64",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_to_uint32",U64_TO_U32,"uint32",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_to_usize",U64_USIZE,"usize",
                new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_dec_lt",U64_LT,"uint8",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_dec_eq",U64_EQ,"uint8",
                new String[]{"uint64","uint64"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_of_nat_mk",U64_OWNED_NAT,"uint64",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_to_utf8",STR_TO_UTF8,"object",
                new String[]{"object"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_to_utf8",STR_TO_UTF8,"object",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_string_from_utf8_unchecked",STR_FROM_UTF8,"object",
                new String[]{"object","erased"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_validate_utf8",STR_VALIDATE_UTF8,"uint8",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_byte_array_copy_slice",BYTE_COPY_SLICE,"object",
                new String[]{"object","tobject","object","tobject","tobject","uint8"},
                new boolean[]{true,false,false,false,false,false}));
        register(registry,new ExternSpec("lean_mk_empty_byte_array",BYTE_EMPTY,"object",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_byte_array_mk",BYTE_MK,"object",
                new String[]{"object"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_byte_array_fget",BYTE_GET,"uint8",
                new String[]{"object","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_byte_array_get",BYTE_GET_DEFAULT,"uint8",
                new String[]{"object","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_io_get_random_bytes",IO_RANDOM_BYTES,"object",
                new String[]{"usize","void"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_byte_array_size",BYTE_SIZE,"tagged",
                new String[]{"object"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_byte_array_push",BYTE_PUSH,"object",
                new String[]{"object","uint8"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_ptr_addr",POINTER_IDENTITY,"usize",
                new String[]{"erased","tobject"},new boolean[]{false,true}));
        register(registry,new ExternSpec("lean_nat_to_int",INT_OF_NAT,"tobject",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_int_neg_succ_of_nat",INT_NEG_SUCC,"tobject",
                new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_int_neg",INT_NEG,"tobject",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_nat_abs",INT_ABS,"tobject",
                new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_int_add",INT_ADD,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_sub",INT_SUB,"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_dec_eq",INT_EQ,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_dec_lt",INT_LT,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_dec_le",INT_LE,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_name_eq",NAME_EQ,"uint8",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_get_githash",BUILD_GITHASH,"object",
                new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_system_platform_target",BUILD_TARGET,"object",
                new String[]{"tagged"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_string_memcmp",STR_MEMCMP,"uint8",
                new String[]{"object","object","tobject","tobject","tobject","erased","erased"},new boolean[]{true,true,true,true,true,false,false}));
        register(registry,new ExternSpec("lean_substring_beq",STR_SUBSTRING_EQ,"uint8",
                new String[]{"object","object"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_posof",STR_POS_OF,"tobject",
                new String[]{"object","uint32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_offsetofpos",STR_OFFSET_OF_POS,"tobject",
                new String[]{"object","tobject"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_string_pushn",STR_PUSHN,"object",
                new String[]{"object","uint32","tobject"},new boolean[]{false,false,false}));
        register(registry,new ExternSpec("lean_float_of_bits",FLOAT_BITS,"float",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_float_to_bits",FLOAT_TO_BITS,"uint64",new String[]{"float"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint64_to_float",FLOAT_U64,"float",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_float_sub",FLOAT_SUB,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_mul",FLOAT_MUL,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_div",FLOAT_DIV,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_beq",FLOAT_EQ,"uint8",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_decLt",FLOAT_LT,"uint8",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_decLe",FLOAT_LE,"uint8",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float_to_string",FLOAT_STRING,"object",new String[]{"float"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint8_add",U8_ADD,"uint8",new String[]{"uint8","uint8"},new boolean[]{false,false}));
        // Signed Int64 is a trivial two's-complement wrapper over the exact UInt64 lane.
        register(registry,new ExternSpec("lean_int64_neg",U64_NEG,"uint64",new String[]{"uint64"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_float_add",FLOAT_ADD,"float",new String[]{"float","float"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float32_add",FLOAT32_ADD,"float32",new String[]{"float32","float32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float32_of_bits",FLOAT32_BITS,"float32",new String[]{"uint32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_float32_to_bits",FLOAT32_TO_BITS,"uint32",new String[]{"float32"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint32_of_nat_mk",U32_OWNED_NAT,"uint32",new String[]{"tobject"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_float32_div",FLOAT32_DIV,"float32",new String[]{"float32","float32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_float32_mul",FLOAT32_MUL,"float32",new String[]{"float32","float32"},new boolean[]{false,false}));
        register(registry,new ExternSpec("lean_uint64_to_float32",U64_FLOAT32,"float32",new String[]{"uint64"},new boolean[]{false}));
        // Pinned Lean 4.33.1 Init IR ABIs: Nat/Int operands are borrowed, proofs erased.
        String[] natBinary={"lean_nat_land","lean_nat_lxor","lean_nat_gcd"};
        int[] natBinaryOps={NAT_AND,NAT_XOR,NAT_GCD};
        for(int i=0;i<natBinary.length;i++) register(registry,new ExternSpec(natBinary[i],natBinaryOps[i],"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_nat_pred",NAT_PRED,"tobject",new String[]{"tobject"},new boolean[]{true}));
        register(registry,new ExternSpec("lean_nat_div_exact",NAT_DIV_EXACT,"tobject",
                new String[]{"tobject","tobject","erased"},new boolean[]{true,true,false}));
        String[] intBinary={"lean_int_mul","lean_int_div","lean_int_mod","lean_int_ediv","lean_int_emod"};
        int[] intBinaryOps={INT_MUL,INT_DIV,INT_MOD,INT_EDIV,INT_EMOD};
        for(int i=0;i<intBinary.length;i++) register(registry,new ExternSpec(intBinary[i],intBinaryOps[i],"tobject",
                new String[]{"tobject","tobject"},new boolean[]{true,true}));
        register(registry,new ExternSpec("lean_int_div_exact",INT_DIV_EXACT,"tobject",
                new String[]{"tobject","tobject","erased"},new boolean[]{true,true,false}));
        register(registry,new ExternSpec("lean_int_dec_nonneg",INT_NONNEG,"uint8",new String[]{"tobject"},new boolean[]{true}));
        // UInt8/UInt16.toBitVec share the Nat conversion symbol with an untagged result type.
        register(registry,new ExternSpec("lean_uint8_to_nat",U8_NAT,"tobject",new String[]{"uint8"},new boolean[]{false}));
        register(registry,new ExternSpec("lean_uint16_to_nat",U16_NAT,"tobject",new String[]{"uint16"},new boolean[]{false}));
        for(int op:new int[]{U8_SUB,U8_MUL,U8_DIV,U8_MOD,U8_OR,U8_XOR,U8_NOT,U8_NEG,U8_SHL,U8_SHR,U8_LOG2,U8_LT,
                U8_TO_U16,U8_TO_USIZE,BOOL_U8,
                U16_ADD,U16_SUB,U16_MUL,U16_DIV,U16_MOD,U16_AND,U16_OR,U16_XOR,U16_NOT,U16_NEG,U16_SHL,U16_SHR,
                U16_LOG2,U16_LT,U16_LE,U16_TO_U8,U16_TO_U32,U16_TO_U64,U16_TO_USIZE,BOOL_U16,
                U32_SUB,U32_MUL,U32_DIV,U32_MOD,U32_AND,U32_OR,U32_XOR,U32_NOT,U32_NEG,U32_SHL,U32_SHR,U32_LOG2,
                U32_TO_U16,U32_TO_USIZE,BOOL_U32,U64_TO_U16,
                USIZE_DIV,USIZE_MOD,USIZE_OR,USIZE_XOR,USIZE_NOT,USIZE_NEG,USIZE_LOG2,USIZE_TO_U8,USIZE_TO_U16,
                USIZE_TO_U32,USIZE_OWNED_NAT,BOOL_USIZE}) registerWord(registry,op);
        // Narrower unsigned lanes reuse the exact UInt64 conversions: each source value is
        // already its unsigned 64-bit pattern, and those conversions round exactly once.
        for(String type:new String[]{"uint8","uint16","uint32","usize"}) {
            register(registry,new ExternSpec("lean_"+type+"_to_float",FLOAT_U64,"float",new String[]{type},new boolean[]{false}));
            register(registry,new ExternSpec("lean_"+type+"_to_float32",U64_FLOAT32,"float32",new String[]{type},new boolean[]{false}));
        }
        registry.replaceAll((symbol,entries)->Collections.unmodifiableList(entries));
        return Collections.unmodifiableMap(registry);
    }
    private static void register(Map<String,List<ExternSpec>> registry,ExternSpec spec) {
        registry.computeIfAbsent(spec.symbol,ignored->new ArrayList<>()).add(spec);
    }
    /** Symbol and ABI follow from the generic word ID; scalar operands are never borrowed. */
    private static void registerWord(Map<String,List<ExternSpec>> registry,int op) {
        require(wordPrimitive(op),"Invalid word extern registry entry");
        int lane=(op-WORD_BASE)/WORD_STRIDE,code=(op-WORD_BASE)%WORD_STRIDE;
        String type=WORD_TYPES[lane],result=type,symbol;
        String[] params;
        if(code==W_FROM_BOOL) { symbol="lean_bool_to_"+type; params=new String[]{"uint8"}; }
        else {
            symbol="lean_"+type+"_"+WORD_SUFFIXES[code];
            if(code==W_OWNED_NAT) params=new String[]{"tobject"};
            else if(code>=W_TO_U8&&code<=W_TO_USIZE) { params=new String[]{type}; result=WORD_TYPES[code-W_TO_U8]; }
            else if(code==W_NOT||code==W_NEG||code==W_LOG2) params=new String[]{type};
            else { params=new String[]{type,type}; if(code>=W_EQ&&code<=W_LE) result="uint8"; }
        }
        register(registry,new ExternSpec(symbol,op,result,params,new boolean[params.length]));
    }
    static Object externSymbol(Map<String,Object> declaration) {
        List<Object> entries=list(map(declaration.get("ext")).get("entries"));
        if(entries.isEmpty()) throw error("Missing extern");
        Map<String,Object> entry=null;
        for(Object raw:entries) {
            Map<String,Object> candidate=map(raw);
            if(candidate.size()!=1) throw error("Invalid extern entry");
            String kind=candidate.keySet().iterator().next(); Map<String,Object> data=map(candidate.get(kind));
            String backend=name(data.get("backend"));
            if(backend.equals("all")||backend.equals("c")) {
                if(!kind.equals("standard")) throw error("Inline extern outside baseline profile");
                entry=data; break;
            }
        }
        if(entry==null) throw error("No supported extern backend");
        return entry.get("fn");
    }
    static ExternSpec resolveExtern(Map<String,Object> declaration) {
        Object symbol=externSymbol(declaration);
        List<ExternSpec> allowed=EXTERNS.get(symbol);
        if(allowed==null) throw error("Unsupported baseline extern: "+symbol);
        for(ExternSpec spec:allowed) if(spec.matches(declaration)) return spec;
        throw error("Captured extern ABI mismatch: "+symbol);
    }
}
