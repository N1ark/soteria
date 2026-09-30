// Lean compiler output
// Module: Tiny.Lib.Int
// Imports: public import Init public meta import Init public import Tiny.Lifts public import Tiny.Lib.Cases
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_subterms(lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__1_value;
LEAN_EXPORT uint8_t lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___boxed(lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tdiv"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 57, 32, 33, 207, 206, 80, 132)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1_value;
static lean_once_cell_t lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__2;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__0_value;
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__1_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__2_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__2 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__2_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Tiny"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value;
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lib"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value;
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "zrem_facts"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__2 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3_value_aux_1),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(146, 145, 18, 26, 20, 235, 129, 236)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3_value;
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "emod_facts"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__4 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__4_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5_value_aux_1),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(92, 131, 171, 203, 74, 136, 123, 47)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zrem"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 40, 82, 141, 157, 105, 51, 122)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__1_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tmod"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 141, 33, 61, 13, 165, 12, 4)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__1_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__0_value;
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__1_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__2_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__2 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__2_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_split"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1_value_aux_1),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 29, 22, 224, 170, 208, 104, 140)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1_value;
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mul_comm"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__2 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 99, 245, 121, 48, 229, 12, 198)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__3 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__3_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tdiv_facts"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1_value_aux_1),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 238, 183, 104, 144, 86, 28, 218)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___closed__0_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "kanon_fact"};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__0 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 152, 14, 219, 165, 241, 20, 220)}};
static const lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__1 = (const lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_kanon__tiny__values_Tiny_Lib_arithFacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_Lib_arithFacts___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_arithFacts___closed__0_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "tacticKanon_arith_facts"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 13, 77, 81, 143, 104, 243, 175)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "kanon_arith_facts"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__3_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__3_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__4_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__4_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______elabRules__Tiny__Lib__tacticKanon__arith__facts__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______elabRules__Tiny__Lib__tacticKanon__arith__facts__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticKanon_arith"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 188, 174, 227, 27, 168, 117, 251)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "kanon_arith"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__3_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__3_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__4_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__4_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__3_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__5 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__5_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__6 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__6_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__8 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__8_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__10 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__10_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__11 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__11_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__12 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__12_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__14 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__14_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__15 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__15_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__17 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__17_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__20 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__20_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__21 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__21_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__22 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__22_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Val.bool.injEq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__24 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__24_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__25;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Val"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bool"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__27 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__27_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(11, 178, 222, 215, 132, 58, 232, 77)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(84, 169, 174, 90, 130, 62, 47, 154)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(48, 84, 10, 92, 156, 224, 10, 149)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(216, 118, 214, 105, 232, 53, 164, 173)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(35, 155, 147, 149, 220, 110, 141, 182)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(19, 172, 168, 134, 206, 79, 40, 155)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__31 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__31_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__32 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__32_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__33 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__33_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Val.int.injEq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__34 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__34_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__35;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "int"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__36 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__36_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(11, 178, 222, 215, 132, 58, 232, 77)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(122, 123, 3, 225, 213, 60, 72, 54)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(182, 173, 204, 142, 89, 169, 82, 231)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(216, 118, 214, 105, 232, 53, 164, 173)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(85, 60, 176, 97, 109, 223, 74, 26)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 132, 14, 100, 63, 179, 169, 255)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__39 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__39_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__40 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__40_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "decide_eq_decide"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__41 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__41_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__42;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(184, 62, 47, 113, 11, 47, 94, 85)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__43 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__43_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__44 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__44_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__44_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__45 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__45_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__46 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__46_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decide_not"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__47 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__47_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__48;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(175, 201, 43, 125, 53, 154, 158, 93)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__49 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__49_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__50 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__50_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__51 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__51_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Int.dvd_iff_tmod_eq_zero"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__52 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__52_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__53;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "dvd_iff_tmod_eq_zero"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__54 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__54_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(239, 215, 247, 225, 137, 109, 23, 19)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__56 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__56_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__57 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__57_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ge_iff_le"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__58 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__58_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__59;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(72, 50, 182, 130, 137, 204, 30, 46)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__60 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__60_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__61 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__61_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__62 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__62_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "gt_iff_lt"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__63 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__63_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__64;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(51, 13, 218, 15, 227, 55, 72, 165)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__65 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__65_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__65_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__66 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__66_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__66_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__67 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__67_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Bool.false_eq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__68 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__68_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__69;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__70 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__70_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "false_eq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__71 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__71_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(152, 6, 91, 171, 239, 182, 176, 147)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__73 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__73_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__73_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__74 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__74_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Bool.true_eq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__75 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__75_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__76;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "true_eq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__77 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__77_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__77_value),LEAN_SCALAR_PTR_LITERAL(179, 147, 178, 212, 67, 206, 176, 189)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__79 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__79_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__79_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__80 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__80_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "decide_eq_false_iff_not"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__81 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__81_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__82;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(114, 97, 46, 181, 212, 187, 217, 163)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__83 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__83_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__83_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__84 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__84_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__84_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__85 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__85_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "decide_eq_true_eq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__86 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__86_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__87;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(36, 171, 12, 14, 206, 183, 248, 192)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__88 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__88_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__88_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__89 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__89_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__89_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__90 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__90_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__91 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__91_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__92 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__92_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__92_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__94 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__94_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__95 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__95_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__97 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__97_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__98 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__98_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__99 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__99_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__99_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "tacticKanon_rule_arith"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value_aux_0),((lean_object*)&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 242, 36, 210, 249, 122, 183, 205)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "kanon_rule_arith"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__3_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__3_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__4_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__4_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Kanon"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Proof"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticKanon_rule_lift"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 122, 127, 234, 44, 103, 195, 155)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 79, 74, 224, 52, 28, 84, 42)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 175, 114, 131, 7, 152, 167, 21)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "kanon_rule_lift"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__4_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__5 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__5_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__7 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__7_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "refine"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__8 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__8_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(49, 130, 130, 160, 131, 48, 178, 245)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__10 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__10_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__11 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__11_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Kanon.Sem.Refines.intro"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__13 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__13_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__14;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sem"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__15 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__15_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Refines"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__16 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__16_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__17 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__17_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 122, 127, 234, 44, 103, 195, 155)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(212, 172, 173, 192, 92, 96, 139, 223)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(227, 136, 177, 129, 178, 209, 84, 144)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(0, 246, 211, 9, 87, 39, 174, 88)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__19 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__19_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__21 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__21_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__22 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__22_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__23 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__23_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__24_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(238, 151, 138, 49, 249, 18, 254, 242)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__24 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__24_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__25 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__25_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__26_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__26 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__26_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__27 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__27_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tacticKanon_wt"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__28 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__28_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 122, 127, 234, 44, 103, 195, 155)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 79, 74, 224, 52, 28, 84, 42)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(31, 150, 155, 29, 105, 191, 138, 250)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "kanon_wt"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__30 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__30_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticKanon_sem_core"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__31 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__31_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 122, 127, 234, 44, 103, 195, 155)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 79, 74, 224, 52, 28, 84, 42)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(48, 72, 133, 87, 155, 97, 205, 252)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "kanon_sem_core"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__33 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__33_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__34 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__34_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__36 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__36_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__37 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__37_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__38 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__38_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticKanon_close"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__39 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__39_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 122, 127, 234, 44, 103, 195, 155)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 79, 74, 224, 52, 28, 84, 42)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(74, 47, 224, 175, 99, 22, 245, 175)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "kanon_close"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__41 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__41_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__42 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__42_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat'"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__44 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__44_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(199, 67, 182, 138, 186, 187, 207, 59)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__46 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__46_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(104, 58, 38, 157, 113, 69, 9, 24)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "locationHyp"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__48 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__48_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(229, 146, 67, 234, 45, 36, 143, 176)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__50 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__50_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__51;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__52 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__52_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__53 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__53_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_subterms(lean_object* v_e_1_, lean_object* v_acc_2_){
_start:
{
lean_object* v_acc_3_; 
lean_inc_ref(v_e_1_);
v_acc_3_ = lean_array_push(v_acc_2_, v_e_1_);
switch(lean_obj_tag(v_e_1_))
{
case 5:
{
lean_object* v_fn_4_; lean_object* v_arg_5_; lean_object* v___x_6_; 
v_fn_4_ = lean_ctor_get(v_e_1_, 0);
lean_inc_ref(v_fn_4_);
v_arg_5_ = lean_ctor_get(v_e_1_, 1);
lean_inc_ref(v_arg_5_);
lean_dec_ref_known(v_e_1_, 2);
v___x_6_ = lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_subterms(v_fn_4_, v_acc_3_);
v_e_1_ = v_arg_5_;
v_acc_2_ = v___x_6_;
goto _start;
}
case 10:
{
lean_object* v_expr_8_; 
v_expr_8_ = lean_ctor_get(v_e_1_, 1);
lean_inc_ref(v_expr_8_);
lean_dec_ref_known(v_e_1_, 2);
v_e_1_ = v_expr_8_;
v_acc_2_ = v_acc_3_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_1_);
return v_acc_3_;
}
}
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp(lean_object* v_n_13_, lean_object* v_e_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(6u);
v___x_16_ = l_Lean_Expr_isAppOfArity(v_e_14_, v_n_13_, v___x_15_);
if (v___x_16_ == 0)
{
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_17_ = l_Lean_Expr_getAppNumArgs(v_e_14_);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_sub(v___x_17_, v___x_18_);
lean_dec(v___x_17_);
v___x_20_ = l_Lean_Expr_getRevArg_x21(v_e_14_, v___x_19_);
v___x_21_ = ((lean_object*)(lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___closed__1));
v___x_22_ = l_Lean_Expr_isConstOf(v___x_20_, v___x_21_);
lean_dec_ref(v___x_20_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp___boxed(lean_object* v_n_23_, lean_object* v_e_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp(v_n_23_, v_e_24_);
lean_dec_ref(v_e_24_);
lean_dec(v_n_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
static lean_object* _init_lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__2(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1));
v___x_33_ = l_Lean_Expr_const___override(v___x_32_, v___x_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11(size_t v_sz_34_, size_t v_i_35_, lean_object* v_bs_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_usize_dec_lt(v_i_35_, v_sz_34_);
if (v___x_37_ == 0)
{
return v_bs_36_;
}
else
{
lean_object* v_v_38_; lean_object* v___x_39_; lean_object* v_bs_x27_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; size_t v___x_49_; size_t v___x_50_; lean_object* v___x_51_; 
v_v_38_ = lean_array_uget(v_bs_36_, v_i_35_);
v___x_39_ = lean_unsigned_to_nat(0u);
v_bs_x27_40_ = lean_array_uset(v_bs_36_, v_i_35_, v___x_39_);
v___x_41_ = lean_obj_once(&lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__2, &lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__2_once, _init_lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__2);
v___x_42_ = l_Lean_Expr_getAppNumArgs(v_v_38_);
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_sub(v___x_42_, v___x_43_);
lean_dec(v___x_42_);
lean_inc(v___x_44_);
v___x_45_ = l_Lean_Expr_getRevArg_x21(v_v_38_, v___x_44_);
v___x_46_ = lean_nat_sub(v___x_44_, v___x_43_);
lean_dec(v___x_44_);
v___x_47_ = l_Lean_Expr_getRevArg_x21(v_v_38_, v___x_46_);
lean_dec(v_v_38_);
v___x_48_ = l_Lean_mkAppB(v___x_41_, v___x_45_, v___x_47_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_35_, v___x_49_);
v___x_51_ = lean_array_uset(v_bs_x27_40_, v_i_35_, v___x_48_);
v_i_35_ = v___x_50_;
v_bs_36_ = v___x_51_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___boxed(lean_object* v_sz_53_, lean_object* v_i_54_, lean_object* v_bs_55_){
_start:
{
size_t v_sz_boxed_56_; size_t v_i_boxed_57_; lean_object* v_res_58_; 
v_sz_boxed_56_ = lean_unbox_usize(v_sz_53_);
lean_dec(v_sz_53_);
v_i_boxed_57_ = lean_unbox_usize(v_i_54_);
lean_dec(v_i_54_);
v_res_58_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11(v_sz_boxed_56_, v_i_boxed_57_, v_bs_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10(lean_object* v_as_64_, size_t v_i_65_, size_t v_stop_66_, lean_object* v_b_67_){
_start:
{
lean_object* v___y_69_; uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_eq(v_i_65_, v_stop_66_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_74_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___closed__2));
v___x_75_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v___x_76_ = lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
else
{
lean_object* v___x_77_; 
lean_inc(v___x_75_);
v___x_77_ = lean_array_push(v_b_67_, v___x_75_);
v___y_69_ = v___x_77_;
goto v___jp_68_;
}
}
else
{
return v_b_67_;
}
v___jp_68_:
{
size_t v___x_70_; size_t v___x_71_; 
v___x_70_ = ((size_t)1ULL);
v___x_71_ = lean_usize_add(v_i_65_, v___x_70_);
v_i_65_ = v___x_71_;
v_b_67_ = v___y_69_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10___boxed(lean_object* v_as_78_, lean_object* v_i_79_, lean_object* v_stop_80_, lean_object* v_b_81_){
_start:
{
size_t v_i_boxed_82_; size_t v_stop_boxed_83_; lean_object* v_res_84_; 
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_stop_boxed_83_ = lean_unbox_usize(v_stop_80_);
lean_dec(v_stop_80_);
v_res_84_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10(v_as_78_, v_i_boxed_82_, v_stop_boxed_83_, v_b_81_);
lean_dec_ref(v_as_78_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg(lean_object* v_as_97_, size_t v_sz_98_, size_t v_i_99_, lean_object* v_b_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_usize_dec_lt(v_i_99_, v_sz_98_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v_b_100_);
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_a_108_ = lean_array_uget_borrowed(v_as_97_, v_i_99_);
v___x_109_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__3));
v___x_110_ = l_Lean_Expr_getAppNumArgs(v_a_108_);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_sub(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
lean_inc(v___x_112_);
v___x_113_ = l_Lean_Expr_getRevArg_x21(v_a_108_, v___x_112_);
v___x_114_ = lean_nat_sub(v___x_112_, v___x_111_);
lean_dec(v___x_112_);
v___x_115_ = l_Lean_Expr_getRevArg_x21(v_a_108_, v___x_114_);
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_116_);
v___x_118_ = lean_array_push(v___x_117_, v___x_113_);
v___x_119_ = lean_array_push(v___x_118_, v___x_115_);
lean_inc_ref(v___x_119_);
v___x_120_ = l_Lean_Meta_mkAppM(v___x_109_, v___x_119_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_122_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5));
v___x_123_ = l_Lean_Meta_mkAppM(v___x_122_, v___x_119_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; lean_object* v___x_126_; size_t v___x_127_; size_t v___x_128_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_123_, 1);
v___x_125_ = lean_array_push(v_b_100_, v_a_121_);
v___x_126_ = lean_array_push(v___x_125_, v_a_124_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_i_99_, v___x_127_);
v_i_99_ = v___x_128_;
v_b_100_ = v___x_126_;
goto _start;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_a_121_);
lean_dec_ref(v_b_100_);
v_a_130_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_123_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_123_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec_ref(v___x_119_);
lean_dec_ref(v_b_100_);
v_a_138_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_120_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_120_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___boxed(lean_object* v_as_146_, lean_object* v_sz_147_, lean_object* v_i_148_, lean_object* v_b_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
size_t v_sz_boxed_155_; size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_sz_boxed_155_ = lean_unbox_usize(v_sz_147_);
lean_dec(v_sz_147_);
v_i_boxed_156_ = lean_unbox_usize(v_i_148_);
lean_dec(v_i_148_);
v_res_157_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg(v_as_146_, v_sz_boxed_155_, v_i_boxed_156_, v_b_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec_ref(v_as_146_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg(lean_object* v_as_158_, size_t v_sz_159_, size_t v_i_160_, lean_object* v_b_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = lean_usize_dec_lt(v_i_160_, v_sz_159_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v_b_161_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_169_ = lean_array_uget_borrowed(v_as_158_, v_i_160_);
v___x_170_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg___closed__5));
v___x_171_ = lean_unsigned_to_nat(4u);
v___x_172_ = l_Lean_Expr_getAppNumArgs(v_a_169_);
v___x_173_ = lean_nat_sub(v___x_172_, v___x_171_);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_sub(v___x_173_, v___x_174_);
lean_dec(v___x_173_);
v___x_176_ = l_Lean_Expr_getRevArg_x21(v_a_169_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(5u);
v___x_178_ = lean_nat_sub(v___x_172_, v___x_177_);
lean_dec(v___x_172_);
v___x_179_ = lean_nat_sub(v___x_178_, v___x_174_);
lean_dec(v___x_178_);
v___x_180_ = l_Lean_Expr_getRevArg_x21(v_a_169_, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = lean_mk_empty_array_with_capacity(v___x_181_);
v___x_183_ = lean_array_push(v___x_182_, v___x_176_);
v___x_184_ = lean_array_push(v___x_183_, v___x_180_);
v___x_185_ = l_Lean_Meta_mkAppM(v___x_170_, v___x_184_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = lean_array_push(v_b_161_, v_a_186_);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_160_, v___x_188_);
v_i_160_ = v___x_189_;
v_b_161_ = v___x_187_;
goto _start;
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v_b_161_);
v_a_191_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_185_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_185_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg___boxed(lean_object* v_as_199_, lean_object* v_sz_200_, lean_object* v_i_201_, lean_object* v_b_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
size_t v_sz_boxed_208_; size_t v_i_boxed_209_; lean_object* v_res_210_; 
v_sz_boxed_208_ = lean_unbox_usize(v_sz_200_);
lean_dec(v_sz_200_);
v_i_boxed_209_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_res_210_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg(v_as_199_, v_sz_boxed_208_, v_i_boxed_209_, v_b_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec_ref(v_as_199_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8(lean_object* v_as_215_, size_t v_i_216_, size_t v_stop_217_, lean_object* v_b_218_){
_start:
{
lean_object* v___y_220_; uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_eq(v_i_216_, v_stop_217_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_225_ = lean_array_uget_borrowed(v_as_215_, v_i_216_);
v___x_226_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___closed__1));
v___x_227_ = lean_unsigned_to_nat(2u);
v___x_228_ = l_Lean_Expr_isAppOfArity(v___x_225_, v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
v___y_220_ = v_b_218_;
goto v___jp_219_;
}
else
{
lean_object* v___x_229_; 
lean_inc(v___x_225_);
v___x_229_ = lean_array_push(v_b_218_, v___x_225_);
v___y_220_ = v___x_229_;
goto v___jp_219_;
}
}
else
{
return v_b_218_;
}
v___jp_219_:
{
size_t v___x_221_; size_t v___x_222_; 
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_216_, v___x_221_);
v_i_216_ = v___x_222_;
v_b_218_ = v___y_220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8___boxed(lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_stop_232_, lean_object* v_b_233_){
_start:
{
size_t v_i_boxed_234_; size_t v_stop_boxed_235_; lean_object* v_res_236_; 
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_235_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_236_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8(v_as_230_, v_i_boxed_234_, v_stop_boxed_235_, v_b_233_);
lean_dec_ref(v_as_230_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg(lean_object* v_as_237_, size_t v_sz_238_, size_t v_i_239_, lean_object* v_b_240_, lean_object* v___y_241_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v_b_240_);
return v___x_244_;
}
else
{
lean_object* v_snd_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_275_; 
v_snd_245_ = lean_ctor_get(v_b_240_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_b_240_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_b_240_, 0);
lean_dec(v_unused_276_);
v___x_247_ = v_b_240_;
v_isShared_248_ = v_isSharedCheck_275_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_snd_245_);
lean_dec(v_b_240_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_275_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v_a_251_; lean_object* v___y_259_; lean_object* v_a_271_; 
v___x_249_ = lean_box(0);
v_a_271_ = lean_array_uget_borrowed(v_as_237_, v_i_239_);
if (lean_obj_tag(v_a_271_) == 0)
{
v_a_251_ = v_snd_245_;
goto v___jp_250_;
}
else
{
lean_object* v_val_272_; uint8_t v___x_273_; 
v_val_272_ = lean_ctor_get(v_a_271_, 0);
v___x_273_ = l_Lean_LocalDecl_isImplementationDetail(v_val_272_);
if (v___x_273_ == 0)
{
lean_object* v_type_274_; 
v_type_274_ = lean_ctor_get(v_val_272_, 3);
lean_inc_ref(v_type_274_);
v___y_259_ = v_type_274_;
goto v___jp_258_;
}
else
{
v_a_251_ = v_snd_245_;
goto v___jp_250_;
}
}
v___jp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_a_251_);
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_253_ = v___x_247_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_a_251_);
v___x_253_ = v_reuseFailAlloc_257_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
size_t v___x_254_; size_t v___x_255_; 
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_239_, v___x_254_);
v_i_239_ = v___x_255_;
v_b_240_ = v___x_253_;
goto _start;
}
}
v___jp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v___y_259_, v___y_241_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = lean_array_push(v_snd_245_, v_a_261_);
v_a_251_ = v___x_262_;
goto v___jp_250_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_del_object(v___x_247_);
lean_dec(v_snd_245_);
v_a_263_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_260_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_260_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg___boxed(lean_object* v_as_277_, lean_object* v_sz_278_, lean_object* v_i_279_, lean_object* v_b_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
size_t v_sz_boxed_283_; size_t v_i_boxed_284_; lean_object* v_res_285_; 
v_sz_boxed_283_ = lean_unbox_usize(v_sz_278_);
lean_dec(v_sz_278_);
v_i_boxed_284_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_res_285_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg(v_as_277_, v_sz_boxed_283_, v_i_boxed_284_, v_b_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v_as_277_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2(lean_object* v_as_286_, size_t v_sz_287_, size_t v_i_288_, lean_object* v_b_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_lt(v_i_288_, v_sz_287_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v_b_289_);
return v___x_300_;
}
else
{
lean_object* v_snd_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_331_; 
v_snd_301_ = lean_ctor_get(v_b_289_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_b_289_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_b_289_, 0);
lean_dec(v_unused_332_);
v___x_303_ = v_b_289_;
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snd_301_);
lean_dec(v_b_289_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_331_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_a_307_; lean_object* v___y_315_; lean_object* v_a_327_; 
v___x_305_ = lean_box(0);
v_a_327_ = lean_array_uget_borrowed(v_as_286_, v_i_288_);
if (lean_obj_tag(v_a_327_) == 0)
{
v_a_307_ = v_snd_301_;
goto v___jp_306_;
}
else
{
lean_object* v_val_328_; uint8_t v___x_329_; 
v_val_328_ = lean_ctor_get(v_a_327_, 0);
v___x_329_ = l_Lean_LocalDecl_isImplementationDetail(v_val_328_);
if (v___x_329_ == 0)
{
lean_object* v_type_330_; 
v_type_330_ = lean_ctor_get(v_val_328_, 3);
lean_inc_ref(v_type_330_);
v___y_315_ = v_type_330_;
goto v___jp_314_;
}
else
{
v_a_307_ = v_snd_301_;
goto v___jp_306_;
}
}
v___jp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_a_307_);
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_309_ = v___x_303_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_a_307_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_288_, v___x_310_);
v___x_312_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg(v_as_286_, v_sz_287_, v___x_311_, v___x_309_, v___y_295_);
return v___x_312_;
}
}
v___jp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v___y_315_, v___y_295_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v___x_318_ = lean_array_push(v_snd_301_, v_a_317_);
v_a_307_ = v___x_318_;
goto v___jp_306_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_del_object(v___x_303_);
lean_dec(v_snd_301_);
v_a_319_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_316_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_316_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2___boxed(lean_object* v_as_333_, lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
size_t v_sz_boxed_346_; size_t v_i_boxed_347_; lean_object* v_res_348_; 
v_sz_boxed_346_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_347_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_348_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2(v_as_333_, v_sz_boxed_346_, v_i_boxed_347_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_as_333_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0(lean_object* v_init_349_, lean_object* v_n_350_, lean_object* v_b_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
if (lean_obj_tag(v_n_350_) == 0)
{
lean_object* v_cs_361_; lean_object* v___x_362_; lean_object* v___x_363_; size_t v_sz_364_; size_t v___x_365_; lean_object* v___x_366_; 
v_cs_361_ = lean_ctor_get(v_n_350_, 0);
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_b_351_);
v_sz_364_ = lean_array_size(v_cs_361_);
v___x_365_ = ((size_t)0ULL);
v___x_366_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__1(v_init_349_, v_cs_361_, v_sz_364_, v___x_365_, v___x_363_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_381_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_381_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_381_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_fst_371_; 
v_fst_371_ = lean_ctor_get(v_a_367_, 0);
if (lean_obj_tag(v_fst_371_) == 0)
{
lean_object* v_snd_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v_snd_372_ = lean_ctor_get(v_a_367_, 1);
lean_inc(v_snd_372_);
lean_dec(v_a_367_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_snd_372_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_373_);
v___x_375_ = v___x_369_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
else
{
lean_object* v_val_377_; lean_object* v___x_379_; 
lean_inc_ref(v_fst_371_);
lean_dec(v_a_367_);
v_val_377_ = lean_ctor_get(v_fst_371_, 0);
lean_inc(v_val_377_);
lean_dec_ref_known(v_fst_371_, 1);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v_val_377_);
v___x_379_ = v___x_369_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_val_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_366_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_366_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_vs_390_; lean_object* v___x_391_; lean_object* v___x_392_; size_t v_sz_393_; size_t v___x_394_; lean_object* v___x_395_; 
v_vs_390_ = lean_ctor_get(v_n_350_, 0);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_b_351_);
v_sz_393_ = lean_array_size(v_vs_390_);
v___x_394_ = ((size_t)0ULL);
v___x_395_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2(v_vs_390_, v_sz_393_, v___x_394_, v___x_392_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_410_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_410_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_410_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_fst_400_; 
v_fst_400_ = lean_ctor_get(v_a_396_, 0);
if (lean_obj_tag(v_fst_400_) == 0)
{
lean_object* v_snd_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_snd_401_ = lean_ctor_get(v_a_396_, 1);
lean_inc(v_snd_401_);
lean_dec(v_a_396_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v_snd_401_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_402_);
v___x_404_ = v___x_398_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v_val_406_; lean_object* v___x_408_; 
lean_inc_ref(v_fst_400_);
lean_dec(v_a_396_);
v_val_406_ = lean_ctor_get(v_fst_400_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_fst_400_, 1);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_val_406_);
v___x_408_ = v___x_398_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_val_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_a_411_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_395_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_395_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__1(lean_object* v_init_419_, lean_object* v_as_420_, size_t v_sz_421_, size_t v_i_422_, lean_object* v_b_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_422_, v_sz_421_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_b_423_);
return v___x_434_;
}
else
{
lean_object* v_snd_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_469_; 
v_snd_435_ = lean_ctor_get(v_b_423_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_b_423_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_b_423_, 0);
lean_dec(v_unused_470_);
v___x_437_ = v_b_423_;
v_isShared_438_ = v_isSharedCheck_469_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snd_435_);
lean_dec(v_b_423_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_469_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_array_uget_borrowed(v_as_420_, v_i_422_);
lean_inc(v_snd_435_);
v___x_440_ = lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0(v_init_419_, v_a_439_, v_snd_435_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_460_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_460_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_460_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_460_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_a_441_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_445_);
v___x_447_ = v___x_437_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_435_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_447_);
v___x_449_ = v___x_443_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
lean_del_object(v___x_443_);
lean_dec(v_snd_435_);
v_a_452_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v_a_441_, 1);
v___x_453_ = lean_box(0);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_a_452_);
lean_ctor_set(v___x_437_, 0, v___x_453_);
v___x_455_ = v___x_437_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_a_452_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
size_t v___x_456_; size_t v___x_457_; 
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_add(v_i_422_, v___x_456_);
v_i_422_ = v___x_457_;
v_b_423_ = v___x_455_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_del_object(v___x_437_);
lean_dec(v_snd_435_);
v_a_461_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_440_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_440_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__1___boxed(lean_object* v_init_471_, lean_object* v_as_472_, lean_object* v_sz_473_, lean_object* v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_473_);
lean_dec(v_sz_473_);
v_i_boxed_486_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_res_487_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__1(v_init_471_, v_as_472_, v_sz_boxed_485_, v_i_boxed_486_, v_b_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v_as_472_);
lean_dec_ref(v_init_471_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0___boxed(lean_object* v_init_488_, lean_object* v_n_489_, lean_object* v_b_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0(v_init_488_, v_n_489_, v_b_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec_ref(v_n_489_);
lean_dec_ref(v_init_488_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg(lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_504_);
return v___x_508_;
}
else
{
lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_539_; 
v_snd_509_ = lean_ctor_get(v_b_504_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_b_504_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_b_504_, 0);
lean_dec(v_unused_540_);
v___x_511_ = v_b_504_;
v_isShared_512_ = v_isSharedCheck_539_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_dec(v_b_504_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_539_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v_a_515_; lean_object* v___y_523_; lean_object* v_a_535_; 
v___x_513_ = lean_box(0);
v_a_535_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
if (lean_obj_tag(v_a_535_) == 0)
{
v_a_515_ = v_snd_509_;
goto v___jp_514_;
}
else
{
lean_object* v_val_536_; uint8_t v___x_537_; 
v_val_536_ = lean_ctor_get(v_a_535_, 0);
v___x_537_ = l_Lean_LocalDecl_isImplementationDetail(v_val_536_);
if (v___x_537_ == 0)
{
lean_object* v_type_538_; 
v_type_538_ = lean_ctor_get(v_val_536_, 3);
lean_inc_ref(v_type_538_);
v___y_523_ = v_type_538_;
goto v___jp_522_;
}
else
{
v_a_515_ = v_snd_509_;
goto v___jp_514_;
}
}
v___jp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_a_515_);
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_a_515_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
size_t v___x_518_; size_t v___x_519_; 
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_503_, v___x_518_);
v_i_503_ = v___x_519_;
v_b_504_ = v___x_517_;
goto _start;
}
}
v___jp_522_:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v___y_523_, v___y_505_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = lean_array_push(v_snd_509_, v_a_525_);
v_a_515_ = v___x_526_;
goto v___jp_514_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_del_object(v___x_511_);
lean_dec(v_snd_509_);
v_a_527_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_524_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_524_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_b_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_548_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_549_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg(v_as_541_, v_sz_boxed_547_, v_i_boxed_548_, v_b_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v_as_541_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1(lean_object* v_as_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v_b_553_);
return v___x_564_;
}
else
{
lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_595_; 
v_snd_565_ = lean_ctor_get(v_b_553_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_b_553_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_b_553_, 0);
lean_dec(v_unused_596_);
v___x_567_ = v_b_553_;
v_isShared_568_ = v_isSharedCheck_595_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_dec(v_b_553_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_595_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v_a_571_; lean_object* v___y_579_; lean_object* v_a_591_; 
v___x_569_ = lean_box(0);
v_a_591_ = lean_array_uget_borrowed(v_as_550_, v_i_552_);
if (lean_obj_tag(v_a_591_) == 0)
{
v_a_571_ = v_snd_565_;
goto v___jp_570_;
}
else
{
lean_object* v_val_592_; uint8_t v___x_593_; 
v_val_592_ = lean_ctor_get(v_a_591_, 0);
v___x_593_ = l_Lean_LocalDecl_isImplementationDetail(v_val_592_);
if (v___x_593_ == 0)
{
lean_object* v_type_594_; 
v_type_594_ = lean_ctor_get(v_val_592_, 3);
lean_inc_ref(v_type_594_);
v___y_579_ = v_type_594_;
goto v___jp_578_;
}
else
{
v_a_571_ = v_snd_565_;
goto v___jp_570_;
}
}
v___jp_570_:
{
lean_object* v___x_573_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_a_571_);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_a_571_);
v___x_573_ = v_reuseFailAlloc_577_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_552_, v___x_574_);
v___x_576_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg(v_as_550_, v_sz_551_, v___x_575_, v___x_573_, v___y_559_);
return v___x_576_;
}
}
v___jp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v___y_579_, v___y_559_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_array_push(v_snd_565_, v_a_581_);
v_a_571_ = v___x_582_;
goto v___jp_570_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_del_object(v___x_567_);
lean_dec(v_snd_565_);
v_a_583_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_580_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1___boxed(lean_object* v_as_597_, lean_object* v_sz_598_, lean_object* v_i_599_, lean_object* v_b_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
size_t v_sz_boxed_610_; size_t v_i_boxed_611_; lean_object* v_res_612_; 
v_sz_boxed_610_ = lean_unbox_usize(v_sz_598_);
lean_dec(v_sz_598_);
v_i_boxed_611_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_res_612_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1(v_as_597_, v_sz_boxed_610_, v_i_boxed_611_, v_b_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v_as_597_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0(lean_object* v_t_613_, lean_object* v_init_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_root_624_; lean_object* v_tail_625_; lean_object* v___x_626_; 
v_root_624_ = lean_ctor_get(v_t_613_, 0);
v_tail_625_ = lean_ctor_get(v_t_613_, 1);
lean_inc_ref(v_init_614_);
v___x_626_ = lp_kanon__tiny__values_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0(v_init_614_, v_root_624_, v_init_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec_ref(v_init_614_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_663_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_663_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_663_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_663_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
if (lean_obj_tag(v_a_627_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; 
v_a_631_ = lean_ctor_get(v_a_627_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v_a_627_, 1);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_a_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_636_; lean_object* v___x_637_; size_t v_sz_638_; size_t v___x_639_; lean_object* v___x_640_; 
lean_del_object(v___x_629_);
v_a_635_ = lean_ctor_get(v_a_627_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v_a_627_, 1);
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_a_635_);
v_sz_638_ = lean_array_size(v_tail_625_);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1(v_tail_625_, v_sz_638_, v___x_639_, v___x_637_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_654_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_654_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_fst_645_; 
v_fst_645_ = lean_ctor_get(v_a_641_, 0);
if (lean_obj_tag(v_fst_645_) == 0)
{
lean_object* v_snd_646_; lean_object* v___x_648_; 
v_snd_646_ = lean_ctor_get(v_a_641_, 1);
lean_inc(v_snd_646_);
lean_dec(v_a_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_snd_646_);
v___x_648_ = v___x_643_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_snd_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
else
{
lean_object* v_val_650_; lean_object* v___x_652_; 
lean_inc_ref(v_fst_645_);
lean_dec(v_a_641_);
v_val_650_ = lean_ctor_get(v_fst_645_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v_fst_645_, 1);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_val_650_);
v___x_652_ = v___x_643_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_val_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v_a_655_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_640_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_640_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_664_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_626_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_626_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0___boxed(lean_object* v_t_672_, lean_object* v_init_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = lp_kanon__tiny__values_Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0(v_t_672_, v_init_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v_t_672_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13(lean_object* v_as_688_, size_t v_i_689_, size_t v_stop_690_, lean_object* v_b_691_){
_start:
{
lean_object* v___y_693_; uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_eq(v_i_689_, v_stop_690_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___y_700_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_698_ = lean_array_uget_borrowed(v_as_688_, v_i_689_);
v___x_702_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11___closed__1));
v___x_703_ = lean_unsigned_to_nat(2u);
v___x_704_ = l_Lean_Expr_isAppOfArity(v___x_698_, v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___closed__1));
v___x_706_ = l_Lean_Expr_isAppOfArity(v___x_698_, v___x_705_, v___x_703_);
v___y_700_ = v___x_706_;
goto v___jp_699_;
}
else
{
v___y_700_ = v___x_704_;
goto v___jp_699_;
}
v___jp_699_:
{
if (v___y_700_ == 0)
{
v___y_693_ = v_b_691_;
goto v___jp_692_;
}
else
{
lean_object* v___x_701_; 
lean_inc(v___x_698_);
v___x_701_ = lean_array_push(v_b_691_, v___x_698_);
v___y_693_ = v___x_701_;
goto v___jp_692_;
}
}
}
else
{
return v_b_691_;
}
v___jp_692_:
{
size_t v___x_694_; size_t v___x_695_; 
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_add(v_i_689_, v___x_694_);
v_i_689_ = v___x_695_;
v_b_691_ = v___y_693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13___boxed(lean_object* v_as_707_, lean_object* v_i_708_, lean_object* v_stop_709_, lean_object* v_b_710_){
_start:
{
size_t v_i_boxed_711_; size_t v_stop_boxed_712_; lean_object* v_res_713_; 
v_i_boxed_711_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_stop_boxed_712_ = lean_unbox_usize(v_stop_709_);
lean_dec(v_stop_709_);
v_res_713_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13(v_as_707_, v_i_boxed_711_, v_stop_boxed_712_, v_b_710_);
lean_dec_ref(v_as_707_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9(lean_object* v_as_719_, size_t v_i_720_, size_t v_stop_721_, lean_object* v_b_722_){
_start:
{
lean_object* v___y_724_; uint8_t v___x_728_; 
v___x_728_ = lean_usize_dec_eq(v_i_720_, v_stop_721_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___closed__2));
v___x_730_ = lean_array_uget_borrowed(v_as_719_, v_i_720_);
v___x_731_ = lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_isIntOp(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
v___y_724_ = v_b_722_;
goto v___jp_723_;
}
else
{
lean_object* v___x_732_; 
lean_inc(v___x_730_);
v___x_732_ = lean_array_push(v_b_722_, v___x_730_);
v___y_724_ = v___x_732_;
goto v___jp_723_;
}
}
else
{
return v_b_722_;
}
v___jp_723_:
{
size_t v___x_725_; size_t v___x_726_; 
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_720_, v___x_725_);
v_i_720_ = v___x_726_;
v_b_722_ = v___y_724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9___boxed(lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_){
_start:
{
size_t v_i_boxed_737_; size_t v_stop_boxed_738_; lean_object* v_res_739_; 
v_i_boxed_737_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_738_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_739_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9(v_as_733_, v_i_boxed_737_, v_stop_boxed_738_, v_b_736_);
lean_dec_ref(v_as_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12(lean_object* v_as_740_, size_t v_i_741_, size_t v_stop_742_, lean_object* v_b_743_){
_start:
{
lean_object* v___y_745_; uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_eq(v_i_741_, v_stop_742_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_uget_borrowed(v_as_740_, v_i_741_);
v___x_751_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_b_743_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_inc(v___x_750_);
v___x_752_ = lean_array_push(v_b_743_, v___x_750_);
v___y_745_ = v___x_752_;
goto v___jp_744_;
}
else
{
v___y_745_ = v_b_743_;
goto v___jp_744_;
}
}
else
{
return v_b_743_;
}
v___jp_744_:
{
size_t v___x_746_; size_t v___x_747_; 
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_741_, v___x_746_);
v_i_741_ = v___x_747_;
v_b_743_ = v___y_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12___boxed(lean_object* v_as_753_, lean_object* v_i_754_, lean_object* v_stop_755_, lean_object* v_b_756_){
_start:
{
size_t v_i_boxed_757_; size_t v_stop_boxed_758_; lean_object* v_res_759_; 
v_i_boxed_757_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_stop_boxed_758_ = lean_unbox_usize(v_stop_755_);
lean_dec(v_stop_755_);
v_res_759_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12(v_as_753_, v_i_boxed_757_, v_stop_boxed_758_, v_b_756_);
lean_dec_ref(v_as_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg(lean_object* v___x_769_, lean_object* v_a_770_, lean_object* v_as_771_, size_t v_sz_772_, size_t v_i_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_a_781_; uint8_t v___x_785_; 
v___x_785_ = lean_usize_dec_lt(v_i_773_, v_sz_772_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v_a_770_);
lean_dec_ref(v___x_769_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_b_774_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_facts_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___x_838_; 
v_a_787_ = lean_array_uget_borrowed(v_as_771_, v_i_773_);
v___x_788_ = lean_unsigned_to_nat(4u);
v___x_789_ = l_Lean_Expr_getAppNumArgs(v_a_787_);
v___x_790_ = lean_nat_sub(v___x_789_, v___x_788_);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_sub(v___x_790_, v___x_791_);
lean_dec(v___x_790_);
v___x_793_ = l_Lean_Expr_getRevArg_x21(v_a_787_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(5u);
v___x_795_ = lean_nat_sub(v___x_789_, v___x_794_);
lean_dec(v___x_789_);
v___x_796_ = lean_nat_sub(v___x_795_, v___x_791_);
lean_dec(v___x_795_);
v___x_797_ = l_Lean_Expr_getRevArg_x21(v_a_787_, v___x_796_);
v___x_838_ = lean_expr_eqv(v___x_793_, v___x_769_);
if (v___x_838_ == 0)
{
v_facts_799_ = v_b_774_;
v___y_800_ = v___y_775_;
v___y_801_ = v___y_776_;
v___y_802_ = v___y_777_;
v___y_803_ = v___y_778_;
goto v___jp_798_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_839_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1));
v___x_840_ = lean_unsigned_to_nat(3u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
lean_inc_ref(v___x_769_);
v___x_842_ = lean_array_push(v___x_841_, v___x_769_);
lean_inc_ref(v___x_797_);
v___x_843_ = lean_array_push(v___x_842_, v___x_797_);
lean_inc_ref(v_a_770_);
v___x_844_ = lean_array_push(v___x_843_, v_a_770_);
v___x_845_ = l_Lean_Meta_mkAppM(v___x_839_, v___x_844_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = lean_array_push(v_b_774_, v_a_846_);
v_facts_799_ = v___x_847_;
v___y_800_ = v___y_775_;
v___y_801_ = v___y_776_;
v___y_802_ = v___y_777_;
v___y_803_ = v___y_778_;
goto v___jp_798_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v___x_797_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v_b_774_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v___x_769_);
v_a_848_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_845_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_845_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
v___jp_798_:
{
uint8_t v___x_804_; 
v___x_804_ = lean_expr_eqv(v___x_797_, v___x_769_);
lean_dec_ref(v___x_797_);
if (v___x_804_ == 0)
{
lean_dec_ref(v___x_793_);
v_a_781_ = v_facts_799_;
goto v___jp_780_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_805_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__1));
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_mk_empty_array_with_capacity(v___x_806_);
lean_inc_ref(v___x_769_);
v___x_808_ = lean_array_push(v___x_807_, v___x_769_);
lean_inc_ref(v___x_793_);
v___x_809_ = lean_array_push(v___x_808_, v___x_793_);
lean_inc_ref(v_a_770_);
v___x_810_ = lean_array_push(v___x_809_, v_a_770_);
v___x_811_ = l_Lean_Meta_mkAppM(v___x_805_, v___x_810_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___closed__3));
v___x_814_ = lean_unsigned_to_nat(2u);
v___x_815_ = lean_mk_empty_array_with_capacity(v___x_814_);
v___x_816_ = lean_array_push(v___x_815_, v___x_793_);
lean_inc_ref(v___x_769_);
v___x_817_ = lean_array_push(v___x_816_, v___x_769_);
v___x_818_ = l_Lean_Meta_mkAppM(v___x_813_, v___x_817_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_array_push(v_facts_799_, v_a_812_);
v___x_821_ = lean_array_push(v___x_820_, v_a_819_);
v_a_781_ = v___x_821_;
goto v___jp_780_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_812_);
lean_dec_ref(v_facts_799_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v___x_769_);
v_a_822_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_818_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_facts_799_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v___x_769_);
v_a_830_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_811_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_811_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
v___jp_780_:
{
size_t v___x_782_; size_t v___x_783_; 
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_add(v_i_773_, v___x_782_);
v_i_773_ = v___x_783_;
v_b_774_ = v_a_781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg___boxed(lean_object* v___x_856_, lean_object* v_a_857_, lean_object* v_as_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_868_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_869_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg(v___x_856_, v_a_857_, v_as_858_, v_sz_boxed_867_, v_i_boxed_868_, v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec_ref(v_as_858_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4(lean_object* v___y_875_, lean_object* v_as_876_, size_t v_sz_877_, size_t v_i_878_, lean_object* v_b_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v___x_889_; 
v___x_889_ = lean_usize_dec_lt(v_i_878_, v_sz_877_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v_b_879_);
return v___x_890_;
}
else
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_a_891_ = lean_array_uget_borrowed(v_as_876_, v_i_878_);
v___x_892_ = l_Lean_Expr_getAppNumArgs(v_a_891_);
v___x_893_ = lean_unsigned_to_nat(1u);
v___x_894_ = lean_nat_sub(v___x_892_, v___x_893_);
lean_dec(v___x_892_);
lean_inc(v___x_894_);
v___x_895_ = l_Lean_Expr_getRevArg_x21(v_a_891_, v___x_894_);
v___x_896_ = lean_nat_sub(v___x_894_, v___x_893_);
lean_dec(v___x_894_);
v___x_897_ = l_Lean_Expr_getRevArg_x21(v_a_891_, v___x_896_);
v___x_898_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___closed__1));
v___x_899_ = lean_unsigned_to_nat(2u);
v___x_900_ = lean_mk_empty_array_with_capacity(v___x_899_);
lean_inc_ref(v___x_897_);
v___x_901_ = lean_array_push(v___x_900_, v___x_897_);
v___x_902_ = lean_array_push(v___x_901_, v___x_895_);
v___x_903_ = l_Lean_Meta_mkAppM(v___x_898_, v___x_902_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_905_; size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = lean_array_push(v_b_879_, v_a_904_);
v_sz_906_ = lean_array_size(v___y_875_);
v___x_907_ = ((size_t)0ULL);
lean_inc(v_a_891_);
v___x_908_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg(v___x_897_, v_a_891_, v___y_875_, v_sz_906_, v___x_907_, v___x_905_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; size_t v___x_910_; size_t v___x_911_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_878_, v___x_910_);
v_i_878_ = v___x_911_;
v_b_879_ = v_a_909_;
goto _start;
}
else
{
return v___x_908_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___x_897_);
lean_dec_ref(v_b_879_);
v_a_913_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_903_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_903_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4___boxed(lean_object* v___y_921_, lean_object* v_as_922_, lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v_sz_boxed_935_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_936_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_937_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4(v___y_921_, v_as_922_, v_sz_boxed_935_, v_i_boxed_936_, v_b_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec_ref(v_as_922_);
lean_dec_ref(v___y_921_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg(lean_object* v_as_938_, size_t v_sz_939_, size_t v_i_940_, lean_object* v_b_941_){
_start:
{
lean_object* v_a_944_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_940_, v_sz_939_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_941_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; uint8_t v___x_951_; 
v_a_950_ = lean_array_uget_borrowed(v_as_938_, v_i_940_);
v___x_951_ = l_Lean_Expr_hasLooseBVars(v_a_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; 
v___x_952_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_b_941_, v_a_950_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_inc(v_a_950_);
v___x_953_ = lean_array_push(v_b_941_, v_a_950_);
v_a_944_ = v___x_953_;
goto v___jp_943_;
}
else
{
v_a_944_ = v_b_941_;
goto v___jp_943_;
}
}
else
{
v_a_944_ = v_b_941_;
goto v___jp_943_;
}
}
v___jp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_940_, v___x_945_);
v_i_940_ = v___x_946_;
v_b_941_ = v_a_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg___boxed(lean_object* v_as_954_, lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_960_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_961_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg(v_as_954_, v_sz_boxed_959_, v_i_boxed_960_, v_b_957_);
lean_dec_ref(v_as_954_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2(lean_object* v_as_964_, size_t v_sz_965_, size_t v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_lt(v_i_966_, v_sz_965_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v_b_967_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_981_; size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; 
v___x_979_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___closed__0));
v_a_980_ = lean_array_uget_borrowed(v_as_964_, v_i_966_);
lean_inc(v_a_980_);
v___x_981_ = lp_kanon__tiny__values___private_Tiny_Lib_Int_0__Tiny_Lib_subterms(v_a_980_, v___x_979_);
v_sz_982_ = lean_array_size(v___x_981_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg(v___x_981_, v_sz_982_, v___x_983_, v_b_967_);
lean_dec_ref(v___x_981_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; size_t v___x_986_; size_t v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_966_, v___x_986_);
v_i_966_ = v___x_987_;
v_b_967_ = v_a_985_;
goto _start;
}
else
{
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___boxed(lean_object* v_as_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
size_t v_sz_boxed_1002_; size_t v_i_boxed_1003_; lean_object* v_res_1004_; 
v_sz_boxed_1002_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_1003_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_1004_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2(v_as_989_, v_sz_boxed_1002_, v_i_boxed_1003_, v_b_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec_ref(v_as_989_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg(lean_object* v_as_1008_, size_t v_sz_1009_, size_t v_i_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1010_, v_sz_1009_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1011_);
return v___x_1018_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_array_uget_borrowed(v_as_1008_, v_i_1010_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v_a_1019_);
v___x_1020_ = lean_infer_type(v_a_1019_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___closed__1));
lean_inc(v_a_1019_);
v___x_1023_ = l_Lean_MVarId_assert(v_b_1011_, v___x_1022_, v_a_1021_, v_a_1019_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Lean_Meta_intro1Core(v_a_1024_, v___x_1017_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_snd_1027_; size_t v___x_1028_; size_t v___x_1029_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_snd_1027_ = lean_ctor_get(v_a_1026_, 1);
lean_inc(v_snd_1027_);
lean_dec(v_a_1026_);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_add(v_i_1010_, v___x_1028_);
v_i_1010_ = v___x_1029_;
v_b_1011_ = v_snd_1027_;
goto _start;
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1025_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1025_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
return v___x_1023_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_b_1011_);
v_a_1039_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1020_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1020_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg___boxed(lean_object* v_as_1047_, lean_object* v_sz_1048_, lean_object* v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1048_);
lean_dec(v_sz_1048_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_res_1058_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg(v_as_1047_, v_sz_boxed_1056_, v_i_boxed_1057_, v_b_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_as_1047_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___lam__0(lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Elab_Tactic_getMainTarget(v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v_lctx_1071_; lean_object* v_a_1072_; lean_object* v_decls_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_suggestInvariant_spec__0___redArg(v_a_1069_, v___y_1064_);
v_lctx_1071_ = lean_ctor_get(v___y_1063_, 2);
v_a_1072_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v___x_1070_);
v_decls_1073_ = lean_ctor_get(v_lctx_1071_, 1);
v___x_1074_ = lean_unsigned_to_nat(1u);
v___x_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
v___x_1076_ = lean_array_push(v___x_1075_, v_a_1072_);
v___x_1077_ = lp_kanon__tiny__values_Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0(v_decls_1073_, v___x_1076_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___x_1121_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = ((lean_object*)(lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2___closed__0));
v_sz_1081_ = lean_array_size(v_a_1078_);
v___x_1082_ = ((size_t)0ULL);
v___x_1121_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__2(v_a_1078_, v_sz_1081_, v___x_1082_, v___x_1080_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1078_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1166_; lean_object* v___y_1174_; uint8_t v___x_1184_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_array_get_size(v_a_1122_);
v___x_1184_ = lean_nat_dec_lt(v___x_1079_, v___x_1123_);
if (v___x_1184_ == 0)
{
v___y_1174_ = v___x_1080_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1185_ == 0)
{
if (v___x_1184_ == 0)
{
v___y_1174_ = v___x_1080_;
goto v___jp_1173_;
}
else
{
size_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_usize_of_nat(v___x_1123_);
v___x_1187_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13(v_a_1122_, v___x_1082_, v___x_1186_, v___x_1080_);
v___y_1174_ = v___x_1187_;
goto v___jp_1173_;
}
}
else
{
size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_usize_of_nat(v___x_1123_);
v___x_1189_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__13(v_a_1122_, v___x_1082_, v___x_1188_, v___x_1080_);
v___y_1174_ = v___x_1189_;
goto v___jp_1173_;
}
}
v___jp_1124_:
{
size_t v_sz_1128_; lean_object* v___x_1129_; 
v_sz_1128_ = lean_array_size(v___y_1126_);
v___x_1129_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__4(v___y_1127_, v___y_1126_, v_sz_1128_, v___x_1082_, v___x_1080_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___y_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; size_t v_sz_1131_; lean_object* v___x_1132_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v_sz_1131_ = lean_array_size(v___y_1125_);
v___x_1132_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg(v___y_1125_, v_sz_1131_, v___x_1082_, v_a_1130_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___y_1125_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; uint8_t v___x_1134_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = lean_nat_dec_lt(v___x_1079_, v___x_1123_);
if (v___x_1134_ == 0)
{
lean_dec(v_a_1122_);
v___y_1084_ = v_a_1133_;
v___y_1085_ = v___x_1080_;
goto v___jp_1083_;
}
else
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1135_ == 0)
{
if (v___x_1134_ == 0)
{
lean_dec(v_a_1122_);
v___y_1084_ = v_a_1133_;
v___y_1085_ = v___x_1080_;
goto v___jp_1083_;
}
else
{
size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_usize_of_nat(v___x_1123_);
v___x_1137_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8(v_a_1122_, v___x_1082_, v___x_1136_, v___x_1080_);
lean_dec(v_a_1122_);
v___y_1084_ = v_a_1133_;
v___y_1085_ = v___x_1137_;
goto v___jp_1083_;
}
}
else
{
size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_usize_of_nat(v___x_1123_);
v___x_1139_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__8(v_a_1122_, v___x_1082_, v___x_1138_, v___x_1080_);
lean_dec(v_a_1122_);
v___y_1084_ = v_a_1133_;
v___y_1085_ = v___x_1139_;
goto v___jp_1083_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_a_1122_);
v_a_1140_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1132_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1132_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v___y_1125_);
lean_dec(v_a_1122_);
v_a_1148_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1129_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1129_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
v___jp_1156_:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_nat_dec_lt(v___x_1079_, v___x_1123_);
if (v___x_1159_ == 0)
{
v___y_1125_ = v___y_1158_;
v___y_1126_ = v___y_1157_;
v___y_1127_ = v___x_1080_;
goto v___jp_1124_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1160_ == 0)
{
if (v___x_1159_ == 0)
{
v___y_1125_ = v___y_1158_;
v___y_1126_ = v___y_1157_;
v___y_1127_ = v___x_1080_;
goto v___jp_1124_;
}
else
{
size_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_usize_of_nat(v___x_1123_);
v___x_1162_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9(v_a_1122_, v___x_1082_, v___x_1161_, v___x_1080_);
v___y_1125_ = v___y_1158_;
v___y_1126_ = v___y_1157_;
v___y_1127_ = v___x_1162_;
goto v___jp_1124_;
}
}
else
{
size_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_usize_of_nat(v___x_1123_);
v___x_1164_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__9(v_a_1122_, v___x_1082_, v___x_1163_, v___x_1080_);
v___y_1125_ = v___y_1158_;
v___y_1126_ = v___y_1157_;
v___y_1127_ = v___x_1164_;
goto v___jp_1124_;
}
}
}
v___jp_1165_:
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_nat_dec_lt(v___x_1079_, v___x_1123_);
if (v___x_1167_ == 0)
{
v___y_1157_ = v___y_1166_;
v___y_1158_ = v___x_1080_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1168_ == 0)
{
if (v___x_1167_ == 0)
{
v___y_1157_ = v___y_1166_;
v___y_1158_ = v___x_1080_;
goto v___jp_1156_;
}
else
{
size_t v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_usize_of_nat(v___x_1123_);
v___x_1170_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10(v_a_1122_, v___x_1082_, v___x_1169_, v___x_1080_);
v___y_1157_ = v___y_1166_;
v___y_1158_ = v___x_1170_;
goto v___jp_1156_;
}
}
else
{
size_t v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_usize_of_nat(v___x_1123_);
v___x_1172_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__10(v_a_1122_, v___x_1082_, v___x_1171_, v___x_1080_);
v___y_1157_ = v___y_1166_;
v___y_1158_ = v___x_1172_;
goto v___jp_1156_;
}
}
}
v___jp_1173_:
{
size_t v_sz_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_sz_1175_ = lean_array_size(v___y_1174_);
v___x_1176_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Tiny_Lib_arithFacts_spec__11(v_sz_1175_, v___x_1082_, v___y_1174_);
v___x_1177_ = lean_array_get_size(v___x_1176_);
v___x_1178_ = lean_nat_dec_lt(v___x_1079_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec_ref(v___x_1176_);
v___y_1166_ = v___x_1080_;
goto v___jp_1165_;
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_nat_dec_le(v___x_1177_, v___x_1177_);
if (v___x_1179_ == 0)
{
if (v___x_1178_ == 0)
{
lean_dec_ref(v___x_1176_);
v___y_1166_ = v___x_1080_;
goto v___jp_1165_;
}
else
{
size_t v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_usize_of_nat(v___x_1177_);
v___x_1181_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12(v___x_1176_, v___x_1082_, v___x_1180_, v___x_1080_);
lean_dec_ref(v___x_1176_);
v___y_1166_ = v___x_1181_;
goto v___jp_1165_;
}
}
else
{
size_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_usize_of_nat(v___x_1177_);
v___x_1183_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Tiny_Lib_arithFacts_spec__12(v___x_1176_, v___x_1082_, v___x_1182_, v___x_1080_);
lean_dec_ref(v___x_1176_);
v___y_1166_ = v___x_1183_;
goto v___jp_1165_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v_a_1190_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1121_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1121_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
v___jp_1083_:
{
size_t v_sz_1086_; lean_object* v___x_1087_; 
v_sz_1086_ = lean_array_size(v___y_1085_);
v___x_1087_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg(v___y_1085_, v_sz_1086_, v___x_1082_, v___y_1084_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___y_1085_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1060_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; size_t v_sz_1091_; lean_object* v___x_1092_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v_sz_1091_ = lean_array_size(v_a_1088_);
v___x_1092_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg(v_a_1088_, v_sz_1091_, v___x_1082_, v_a_1090_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v_a_1088_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1095_, v___y_1060_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1092_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1092_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_a_1088_);
v_a_1105_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1089_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1089_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1087_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1087_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1077_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1077_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1068_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1068_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___lam__0___boxed(lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = lp_kanon__tiny__values_Tiny_Lib_arithFacts___lam__0(v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts(lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___f_1234_; lean_object* v___x_1235_; 
v___f_1234_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_arithFacts___closed__0));
v___x_1235_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1234_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib_arithFacts___boxed(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = lp_kanon__tiny__values_Tiny_Lib_arithFacts(v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1(lean_object* v_as_1246_, size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___redArg(v_as_1246_, v_sz_1247_, v_i_1248_, v_b_1249_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1___boxed(lean_object* v_as_1260_, lean_object* v_sz_1261_, lean_object* v_i_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
size_t v_sz_boxed_1273_; size_t v_i_boxed_1274_; lean_object* v_res_1275_; 
v_sz_boxed_1273_ = lean_unbox_usize(v_sz_1261_);
lean_dec(v_sz_1261_);
v_i_boxed_1274_ = lean_unbox_usize(v_i_1262_);
lean_dec(v_i_1262_);
v_res_1275_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__1(v_as_1260_, v_sz_boxed_1273_, v_i_boxed_1274_, v_b_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_as_1260_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3(lean_object* v___x_1276_, lean_object* v_a_1277_, lean_object* v_as_1278_, size_t v_sz_1279_, size_t v_i_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___redArg(v___x_1276_, v_a_1277_, v_as_1278_, v_sz_1279_, v_i_1280_, v_b_1281_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3___boxed(lean_object* v___x_1292_, lean_object* v_a_1293_, lean_object* v_as_1294_, lean_object* v_sz_1295_, lean_object* v_i_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1295_);
lean_dec(v_sz_1295_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1296_);
lean_dec(v_i_1296_);
v_res_1309_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__3(v___x_1292_, v_a_1293_, v_as_1294_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_as_1294_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5(lean_object* v_as_1310_, size_t v_sz_1311_, size_t v_i_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___redArg(v_as_1310_, v_sz_1311_, v_i_1312_, v_b_1313_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5___boxed(lean_object* v_as_1324_, lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
size_t v_sz_boxed_1337_; size_t v_i_boxed_1338_; lean_object* v_res_1339_; 
v_sz_boxed_1337_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1338_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1339_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__5(v_as_1324_, v_sz_boxed_1337_, v_i_boxed_1338_, v_b_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v_as_1324_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6(lean_object* v_as_1340_, size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___redArg(v_as_1340_, v_sz_1341_, v_i_1342_, v_b_1343_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6___boxed(lean_object* v_as_1354_, lean_object* v_sz_1355_, lean_object* v_i_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1355_);
lean_dec(v_sz_1355_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1356_);
lean_dec(v_i_1356_);
v_res_1369_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__6(v_as_1354_, v_sz_boxed_1367_, v_i_boxed_1368_, v_b_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_as_1354_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7(lean_object* v_as_1370_, size_t v_sz_1371_, size_t v_i_1372_, lean_object* v_b_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___redArg(v_as_1370_, v_sz_1371_, v_i_1372_, v_b_1373_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7___boxed(lean_object* v_as_1384_, lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_sz_boxed_1397_; size_t v_i_boxed_1398_; lean_object* v_res_1399_; 
v_sz_boxed_1397_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1398_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1399_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Tiny_Lib_arithFacts_spec__7(v_as_1384_, v_sz_boxed_1397_, v_i_boxed_1398_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_as_1384_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4(lean_object* v_as_1400_, size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_b_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___redArg(v_as_1400_, v_sz_1401_, v_i_1402_, v_b_1403_, v___y_1409_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1414_, lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
size_t v_sz_boxed_1427_; size_t v_i_boxed_1428_; lean_object* v_res_1429_; 
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1428_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1429_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__1_spec__4(v_as_1414_, v_sz_boxed_1427_, v_i_boxed_1428_, v_b_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_as_1414_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16(lean_object* v_as_1430_, size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___redArg(v_as_1430_, v_sz_1431_, v_i_1432_, v_b_1433_, v___y_1439_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16___boxed(lean_object* v_as_1444_, lean_object* v_sz_1445_, lean_object* v_i_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
size_t v_sz_boxed_1457_; size_t v_i_boxed_1458_; lean_object* v_res_1459_; 
v_sz_boxed_1457_ = lean_unbox_usize(v_sz_1445_);
lean_dec(v_sz_1445_);
v_i_boxed_1458_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_res_1459_ = lp_kanon__tiny__values___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Tiny_Lib_arithFacts_spec__0_spec__0_spec__2_spec__16(v_as_1444_, v_sz_boxed_1457_, v_i_boxed_1458_, v_b_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec_ref(v_as_1444_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______elabRules__Tiny__Lib__tacticKanon__arith__facts__1(lean_object* v_x_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1));
v___x_1485_ = l_Lean_Syntax_isOfKind(v_x_1474_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
return v___x_1486_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = lp_kanon__tiny__values_Tiny_Lib_arithFacts(v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______elabRules__Tiny__Lib__tacticKanon__arith__facts__1___boxed(lean_object* v_x_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______elabRules__Tiny__Lib__tacticKanon__arith__facts__1(v_x_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1498_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19(void){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Array_mkArray0(lean_box(0));
return v___x_1557_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__25(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__24));
v___x_1568_ = l_String_toRawSubstring_x27(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__35(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__34));
v___x_1590_ = l_String_toRawSubstring_x27(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__42(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__41));
v___x_1609_ = l_String_toRawSubstring_x27(v___x_1608_);
return v___x_1609_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__48(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__47));
v___x_1621_ = l_String_toRawSubstring_x27(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__53(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__52));
v___x_1632_ = l_String_toRawSubstring_x27(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__59(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__58));
v___x_1645_ = l_String_toRawSubstring_x27(v___x_1644_);
return v___x_1645_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__64(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__63));
v___x_1656_ = l_String_toRawSubstring_x27(v___x_1655_);
return v___x_1656_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__69(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__68));
v___x_1667_ = l_String_toRawSubstring_x27(v___x_1666_);
return v___x_1667_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__76(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__75));
v___x_1681_ = l_String_toRawSubstring_x27(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__82(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__81));
v___x_1694_ = l_String_toRawSubstring_x27(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__87(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__86));
v___x_1705_ = l_String_toRawSubstring_x27(v___x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1(lean_object* v_x_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1));
v___x_1740_ = l_Lean_Syntax_isOfKind(v_x_1736_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_box(1);
v___x_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v_a_1738_);
return v___x_1742_;
}
else
{
lean_object* v_quotContext_1743_; lean_object* v_currMacroScope_1744_; lean_object* v_ref_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_quotContext_1743_ = lean_ctor_get(v_a_1737_, 1);
v_currMacroScope_1744_ = lean_ctor_get(v_a_1737_, 2);
v_ref_1745_ = lean_ctor_get(v_a_1737_, 5);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_SourceInfo_fromRef(v_ref_1745_, v___x_1746_);
v___x_1748_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4));
v___x_1749_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__5));
lean_inc_n(v___x_1747_, 58);
v___x_1750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1747_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7));
v___x_1752_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9));
v___x_1753_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__11));
v___x_1754_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__13));
v___x_1755_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__14));
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1747_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__15));
v___x_1758_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__16));
v___x_1759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1747_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
v___x_1760_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__18));
v___x_1761_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19);
v___x_1762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1747_);
lean_ctor_set(v___x_1762_, 1, v___x_1753_);
lean_ctor_set(v___x_1762_, 2, v___x_1761_);
lean_inc_ref_n(v___x_1762_, 24);
v___x_1763_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1760_, v___x_1762_);
v___x_1764_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__20));
v___x_1765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1747_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1753_, v___x_1765_);
v___x_1767_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__21));
v___x_1768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1747_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__23));
v___x_1770_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__25, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__25_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__25);
v___x_1771_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__29));
lean_inc_n(v_currMacroScope_1744_, 11);
lean_inc_n(v_quotContext_1743_, 11);
v___x_1772_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1771_, v_currMacroScope_1744_);
v___x_1773_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__32));
v___x_1774_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1747_);
lean_ctor_set(v___x_1774_, 1, v___x_1770_);
lean_ctor_set(v___x_1774_, 2, v___x_1772_);
lean_ctor_set(v___x_1774_, 3, v___x_1773_);
v___x_1775_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1774_);
v___x_1776_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__33));
v___x_1777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1747_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__35, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__35_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__35);
v___x_1779_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__37));
v___x_1780_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1779_, v_currMacroScope_1744_);
v___x_1781_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__40));
v___x_1782_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1747_);
lean_ctor_set(v___x_1782_, 1, v___x_1778_);
lean_ctor_set(v___x_1782_, 2, v___x_1780_);
lean_ctor_set(v___x_1782_, 3, v___x_1781_);
v___x_1783_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1782_);
v___x_1784_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__42, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__42_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__42);
v___x_1785_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__43));
v___x_1786_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1785_, v_currMacroScope_1744_);
v___x_1787_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__45));
v___x_1788_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1747_);
lean_ctor_set(v___x_1788_, 1, v___x_1784_);
lean_ctor_set(v___x_1788_, 2, v___x_1786_);
lean_ctor_set(v___x_1788_, 3, v___x_1787_);
v___x_1789_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1788_);
v___x_1790_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__46));
v___x_1791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1747_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1753_, v___x_1791_);
v___x_1793_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__48, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__48_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__48);
v___x_1794_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__49));
v___x_1795_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1794_, v_currMacroScope_1744_);
v___x_1796_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__51));
v___x_1797_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1747_);
lean_ctor_set(v___x_1797_, 1, v___x_1793_);
lean_ctor_set(v___x_1797_, 2, v___x_1795_);
lean_ctor_set(v___x_1797_, 3, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1792_, v___x_1797_);
v___x_1799_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__53, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__53_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__53);
v___x_1800_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__55));
v___x_1801_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1800_, v_currMacroScope_1744_);
v___x_1802_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__57));
v___x_1803_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1747_);
lean_ctor_set(v___x_1803_, 1, v___x_1799_);
lean_ctor_set(v___x_1803_, 2, v___x_1801_);
lean_ctor_set(v___x_1803_, 3, v___x_1802_);
v___x_1804_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1803_);
v___x_1805_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__59, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__59_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__59);
v___x_1806_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__60));
v___x_1807_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1806_, v_currMacroScope_1744_);
v___x_1808_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__62));
v___x_1809_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1747_);
lean_ctor_set(v___x_1809_, 1, v___x_1805_);
lean_ctor_set(v___x_1809_, 2, v___x_1807_);
lean_ctor_set(v___x_1809_, 3, v___x_1808_);
v___x_1810_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1809_);
v___x_1811_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__64, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__64_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__64);
v___x_1812_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__65));
v___x_1813_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1812_, v_currMacroScope_1744_);
v___x_1814_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__67));
v___x_1815_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1747_);
lean_ctor_set(v___x_1815_, 1, v___x_1811_);
lean_ctor_set(v___x_1815_, 2, v___x_1813_);
lean_ctor_set(v___x_1815_, 3, v___x_1814_);
v___x_1816_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1815_);
v___x_1817_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__69, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__69_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__69);
v___x_1818_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__72));
v___x_1819_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1818_, v_currMacroScope_1744_);
v___x_1820_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__74));
v___x_1821_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1747_);
lean_ctor_set(v___x_1821_, 1, v___x_1817_);
lean_ctor_set(v___x_1821_, 2, v___x_1819_);
lean_ctor_set(v___x_1821_, 3, v___x_1820_);
v___x_1822_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1821_);
v___x_1823_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__76, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__76_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__76);
v___x_1824_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__78));
v___x_1825_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1824_, v_currMacroScope_1744_);
v___x_1826_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__80));
v___x_1827_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1747_);
lean_ctor_set(v___x_1827_, 1, v___x_1823_);
lean_ctor_set(v___x_1827_, 2, v___x_1825_);
lean_ctor_set(v___x_1827_, 3, v___x_1826_);
v___x_1828_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1827_);
v___x_1829_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__82, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__82_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__82);
v___x_1830_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__83));
v___x_1831_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1830_, v_currMacroScope_1744_);
v___x_1832_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__85));
v___x_1833_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1747_);
lean_ctor_set(v___x_1833_, 1, v___x_1829_);
lean_ctor_set(v___x_1833_, 2, v___x_1831_);
lean_ctor_set(v___x_1833_, 3, v___x_1832_);
v___x_1834_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1833_);
v___x_1835_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__87, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__87_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__87);
v___x_1836_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__88));
v___x_1837_ = l_Lean_addMacroScope(v_quotContext_1743_, v___x_1836_, v_currMacroScope_1744_);
v___x_1838_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__90));
v___x_1839_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1747_);
lean_ctor_set(v___x_1839_, 1, v___x_1835_);
lean_ctor_set(v___x_1839_, 2, v___x_1837_);
lean_ctor_set(v___x_1839_, 3, v___x_1838_);
v___x_1840_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1769_, v___x_1762_, v___x_1762_, v___x_1839_);
v___x_1841_ = lean_unsigned_to_nat(21u);
v___x_1842_ = lean_mk_empty_array_with_capacity(v___x_1841_);
v___x_1843_ = lean_array_push(v___x_1842_, v___x_1775_);
lean_inc_ref_n(v___x_1777_, 9);
v___x_1844_ = lean_array_push(v___x_1843_, v___x_1777_);
v___x_1845_ = lean_array_push(v___x_1844_, v___x_1783_);
v___x_1846_ = lean_array_push(v___x_1845_, v___x_1777_);
v___x_1847_ = lean_array_push(v___x_1846_, v___x_1789_);
v___x_1848_ = lean_array_push(v___x_1847_, v___x_1777_);
v___x_1849_ = lean_array_push(v___x_1848_, v___x_1798_);
v___x_1850_ = lean_array_push(v___x_1849_, v___x_1777_);
v___x_1851_ = lean_array_push(v___x_1850_, v___x_1804_);
v___x_1852_ = lean_array_push(v___x_1851_, v___x_1777_);
v___x_1853_ = lean_array_push(v___x_1852_, v___x_1810_);
v___x_1854_ = lean_array_push(v___x_1853_, v___x_1777_);
v___x_1855_ = lean_array_push(v___x_1854_, v___x_1816_);
v___x_1856_ = lean_array_push(v___x_1855_, v___x_1777_);
v___x_1857_ = lean_array_push(v___x_1856_, v___x_1822_);
v___x_1858_ = lean_array_push(v___x_1857_, v___x_1777_);
v___x_1859_ = lean_array_push(v___x_1858_, v___x_1828_);
v___x_1860_ = lean_array_push(v___x_1859_, v___x_1777_);
v___x_1861_ = lean_array_push(v___x_1860_, v___x_1834_);
v___x_1862_ = lean_array_push(v___x_1861_, v___x_1777_);
v___x_1863_ = lean_array_push(v___x_1862_, v___x_1840_);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1747_);
lean_ctor_set(v___x_1864_, 1, v___x_1753_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
v___x_1865_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__91));
v___x_1866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1747_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1753_, v___x_1768_, v___x_1864_, v___x_1866_);
v___x_1868_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93));
v___x_1869_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__94));
v___x_1870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1747_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__96));
v___x_1872_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__97));
v___x_1873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1747_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1871_, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1868_, v___x_1870_, v___x_1874_);
v___x_1876_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1753_, v___x_1875_);
lean_inc(v___x_1763_);
v___x_1877_ = l_Lean_Syntax_node6(v___x_1747_, v___x_1758_, v___x_1759_, v___x_1763_, v___x_1762_, v___x_1766_, v___x_1867_, v___x_1876_);
v___x_1878_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1753_, v___x_1877_);
v___x_1879_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1752_, v___x_1878_);
v___x_1880_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1751_, v___x_1879_);
v___x_1881_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1754_, v___x_1756_, v___x_1880_);
v___x_1882_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1753_, v___x_1881_);
v___x_1883_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1752_, v___x_1882_);
v___x_1884_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1751_, v___x_1883_);
v___x_1885_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__98));
v___x_1886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1747_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
lean_inc_ref(v___x_1886_);
lean_inc_ref(v___x_1750_);
v___x_1887_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1748_, v___x_1750_, v___x_1884_, v___x_1886_);
v___x_1888_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__1));
v___x_1889_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith__facts___closed__2));
v___x_1890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1747_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1888_, v___x_1890_);
v___x_1892_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__99));
v___x_1893_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__100));
v___x_1894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1747_);
lean_ctor_set(v___x_1894_, 1, v___x_1892_);
v___x_1895_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1893_, v___x_1894_, v___x_1763_);
v___x_1896_ = l_Lean_Syntax_node5(v___x_1747_, v___x_1753_, v___x_1887_, v___x_1762_, v___x_1891_, v___x_1762_, v___x_1895_);
v___x_1897_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1752_, v___x_1896_);
v___x_1898_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1751_, v___x_1897_);
v___x_1899_ = l_Lean_Syntax_node3(v___x_1747_, v___x_1748_, v___x_1750_, v___x_1898_, v___x_1886_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v_a_1738_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___boxed(lean_object* v_x_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1(v_x_1901_, v_a_1902_, v_a_1903_);
lean_dec_ref(v_a_1902_);
return v_res_1904_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__14(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__13));
v___x_1949_ = l_String_toRawSubstring_x27(v___x_1948_);
return v___x_1949_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__51(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__50));
v___x_2029_ = l_String_toRawSubstring_x27(v___x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1(lean_object* v_x_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__rule__arith___closed__1));
v___x_2037_ = l_Lean_Syntax_isOfKind(v_x_2033_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_box(1);
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_a_2035_);
return v___x_2039_;
}
else
{
lean_object* v_ref_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_ref_2040_ = lean_ctor_get(v_a_2034_, 5);
v___x_2041_ = 0;
v___x_2042_ = l_Lean_SourceInfo_fromRef(v_ref_2040_, v___x_2041_);
v___x_2043_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__4));
v___x_2044_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__5));
lean_inc_n(v___x_2042_, 98);
v___x_2045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2042_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__7));
v___x_2047_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__9));
v___x_2048_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__11));
v___x_2049_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__3));
v___x_2050_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__4));
v___x_2051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2042_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2049_, v___x_2051_);
v___x_2053_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__19);
v___x_2054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2042_);
lean_ctor_set(v___x_2054_, 1, v___x_2048_);
lean_ctor_set(v___x_2054_, 2, v___x_2053_);
v___x_2055_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__6));
v___x_2056_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__7));
v___x_2057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2042_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__8));
v___x_2059_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__9));
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2042_);
lean_ctor_set(v___x_2060_, 1, v___x_2058_);
v___x_2061_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__12));
v___x_2062_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__14, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__14_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__14);
v___x_2063_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__18));
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2042_);
lean_ctor_set(v___x_2065_, 1, v___x_2062_);
lean_ctor_set(v___x_2065_, 2, v___x_2063_);
lean_ctor_set(v___x_2065_, 3, v___x_2064_);
v___x_2066_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__20));
v___x_2067_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__21));
v___x_2068_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2042_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__22));
v___x_2070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2042_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2066_, v___x_2068_, v___x_2070_);
lean_inc(v___x_2071_);
v___x_2072_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2048_, v___x_2071_, v___x_2071_);
v___x_2073_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2061_, v___x_2065_, v___x_2072_);
v___x_2074_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2059_, v___x_2060_, v___x_2073_);
v___x_2075_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__24));
v___x_2076_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__26));
v___x_2077_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__27));
v___x_2078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2042_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2076_, v___x_2078_);
v___x_2080_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__29));
v___x_2081_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__30));
v___x_2082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2042_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2080_, v___x_2082_);
v___x_2084_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2083_);
v___x_2085_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2084_);
v___x_2086_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2085_);
lean_inc(v___x_2079_);
v___x_2087_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2075_, v___x_2079_, v___x_2086_);
v___x_2088_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__32));
v___x_2089_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__33));
v___x_2090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2042_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2088_, v___x_2090_);
v___x_2092_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__34));
v___x_2093_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__35));
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2042_);
lean_ctor_set(v___x_2094_, 1, v___x_2092_);
v___x_2095_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__37));
v___x_2096_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__38));
v___x_2097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2042_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__40));
v___x_2099_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__41));
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2042_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2098_, v___x_2100_);
v___x_2102_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2101_);
v___x_2103_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2102_);
v___x_2104_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2103_);
lean_inc_ref_n(v___x_2097_, 2);
v___x_2105_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2095_, v___x_2097_, v___x_2104_);
v___x_2106_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__1));
v___x_2107_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib_tacticKanon__arith___closed__2));
v___x_2108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2042_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2106_, v___x_2108_);
v___x_2110_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2109_);
v___x_2111_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2110_);
v___x_2112_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2111_);
v___x_2113_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2095_, v___x_2097_, v___x_2112_);
v___x_2114_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__43));
v___x_2115_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__44));
v___x_2116_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__45));
v___x_2117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2042_);
lean_ctor_set(v___x_2117_, 1, v___x_2115_);
v___x_2118_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__46));
v___x_2119_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__47));
v___x_2120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2042_);
lean_ctor_set(v___x_2120_, 1, v___x_2118_);
v___x_2121_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__93));
v___x_2122_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__94));
v___x_2123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2042_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__49));
v___x_2125_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__51, &lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__51_once, _init_lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__51);
v___x_2126_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__52));
v___x_2127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2042_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v___x_2126_);
lean_ctor_set(v___x_2127_, 3, v___x_2064_);
v___x_2128_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2127_);
v___x_2129_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2124_, v___x_2128_);
v___x_2130_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2121_, v___x_2123_, v___x_2129_);
v___x_2131_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2130_);
lean_inc_ref_n(v___x_2054_, 6);
lean_inc_ref(v___x_2120_);
v___x_2132_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2119_, v___x_2120_, v___x_2054_, v___x_2131_);
v___x_2133_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2132_);
v___x_2134_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2133_);
v___x_2135_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2134_);
lean_inc_ref(v___x_2117_);
v___x_2136_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2116_, v___x_2117_, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2136_);
v___x_2138_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2137_);
v___x_2139_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2138_);
v___x_2140_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__arith__1___closed__98));
v___x_2141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2042_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
lean_inc_ref_n(v___x_2141_, 4);
lean_inc_ref_n(v___x_2045_, 4);
v___x_2142_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2043_, v___x_2045_, v___x_2139_, v___x_2141_);
v___x_2143_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___closed__53));
v___x_2144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2042_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2119_, v___x_2120_, v___x_2054_, v___x_2054_);
v___x_2146_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2145_);
v___x_2147_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2146_);
v___x_2148_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2147_);
v___x_2149_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2116_, v___x_2117_, v___x_2148_);
v___x_2150_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2149_);
v___x_2151_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2150_);
v___x_2152_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2151_);
v___x_2153_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2043_, v___x_2045_, v___x_2152_, v___x_2141_);
lean_inc_ref(v___x_2144_);
v___x_2154_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2114_, v___x_2142_, v___x_2144_, v___x_2153_);
lean_inc(v___x_2113_);
lean_inc(v___x_2105_);
v___x_2155_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2048_, v___x_2105_, v___x_2113_);
lean_inc_ref(v___x_2094_);
v___x_2156_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2093_, v___x_2094_, v___x_2155_);
v___x_2157_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2114_, v___x_2154_, v___x_2144_, v___x_2156_);
v___x_2158_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2158_);
v___x_2160_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2159_);
v___x_2161_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2043_, v___x_2045_, v___x_2160_, v___x_2141_);
v___x_2162_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2161_);
v___x_2163_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2162_);
v___x_2164_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2095_, v___x_2097_, v___x_2164_);
v___x_2166_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2048_, v___x_2105_, v___x_2113_, v___x_2165_);
v___x_2167_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2093_, v___x_2094_, v___x_2166_);
v___x_2168_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2167_);
v___x_2169_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2168_);
v___x_2170_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2169_);
lean_inc_ref(v___x_2057_);
v___x_2171_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2055_, v___x_2057_, v___x_2170_);
v___x_2172_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2048_, v___x_2091_, v___x_2054_, v___x_2171_);
v___x_2173_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2172_);
v___x_2174_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2173_);
v___x_2175_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2075_, v___x_2079_, v___x_2174_);
v___x_2176_ = l_Lean_Syntax_node5(v___x_2042_, v___x_2048_, v___x_2074_, v___x_2054_, v___x_2087_, v___x_2054_, v___x_2175_);
v___x_2177_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2176_);
v___x_2178_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2177_);
v___x_2179_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2043_, v___x_2045_, v___x_2178_, v___x_2141_);
v___x_2180_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2048_, v___x_2179_);
v___x_2181_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2180_);
v___x_2182_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2181_);
v___x_2183_ = l_Lean_Syntax_node2(v___x_2042_, v___x_2055_, v___x_2057_, v___x_2182_);
v___x_2184_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2048_, v___x_2052_, v___x_2054_, v___x_2183_);
v___x_2185_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2047_, v___x_2184_);
v___x_2186_ = l_Lean_Syntax_node1(v___x_2042_, v___x_2046_, v___x_2185_);
v___x_2187_ = l_Lean_Syntax_node3(v___x_2042_, v___x_2043_, v___x_2045_, v___x_2186_, v___x_2141_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v_a_2035_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1___boxed(lean_object* v_x_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Int______macroRules__Tiny__Lib__tacticKanon__rule__arith__1(v_x_2189_, v_a_2190_, v_a_2191_);
lean_dec_ref(v_a_2190_);
return v_res_2192_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Lifts(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Lib_Cases(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Lib_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_kanon__tiny__values_Tiny_Lifts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_kanon__tiny__values_Tiny_Lib_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
