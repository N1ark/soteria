// Lean compiler output
// Module: Tiny.Lib.Rule
// Imports: public import Init public meta import Init public import Tiny.Lib.Int
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tacticKanon_auto"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 126, 18, 206, 26, 232, 231, 198)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__5 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__5_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__7 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__7_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__8 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__8_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__9 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__9_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__10 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__10_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__11 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__11_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__12 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__12_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__14 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__14_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__16 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__16_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__18 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__18_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Kanon"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__19 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__19_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Proof"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__20 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__20_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tacticKanon_rule"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__21 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__21_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(116, 122, 127, 234, 44, 103, 195, 155)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(23, 79, 74, 224, 52, 28, 84, 42)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(168, 1, 30, 186, 56, 253, 163, 7)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "kanon_rule"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__23 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__23_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__24 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__24_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__25 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__25_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value_aux_2),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__27 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__27_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Tiny"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__28 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__28_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lib"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__29 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__29_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "tacticKanon_rule_arith"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__30 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__30_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(220, 86, 205, 131, 147, 23, 200, 53)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31_value_aux_0),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 63, 225, 232, 14, 100, 208)}};
static const lean_ctor_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31_value_aux_1),((lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(237, 242, 36, 210, 249, 122, 183, 205)}};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "kanon_rule_arith"};
static const lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__32 = (const lean_object*)&lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__32_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1(lean_object* v_x_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__1));
v___x_67_ = l_Lean_Syntax_isOfKind(v_x_63_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_box(1);
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_a_65_);
return v___x_69_;
}
else
{
lean_object* v_ref_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_ref_70_ = lean_ctor_get(v_a_64_, 5);
v___x_71_ = 0;
v___x_72_ = l_Lean_SourceInfo_fromRef(v_ref_70_, v___x_71_);
v___x_73_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__5));
v___x_74_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__6));
lean_inc_n(v___x_72_, 28);
v___x_75_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
v___x_76_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__8));
v___x_77_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__10));
v___x_78_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__11));
v___x_79_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_72_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__13));
v___x_81_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__15));
v___x_82_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__17));
v___x_83_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__18));
v___x_84_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_72_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__22));
v___x_86_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__23));
v___x_87_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_72_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Lean_Syntax_node1(v___x_72_, v___x_85_, v___x_87_);
v___x_89_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__24));
v___x_90_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_72_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__25));
v___x_92_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__26));
v___x_93_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_72_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
v___x_94_ = l_Lean_Syntax_node1(v___x_72_, v___x_92_, v___x_93_);
lean_inc(v___x_94_);
lean_inc_ref(v___x_90_);
v___x_95_ = l_Lean_Syntax_node3(v___x_72_, v___x_76_, v___x_88_, v___x_90_, v___x_94_);
v___x_96_ = l_Lean_Syntax_node1(v___x_72_, v___x_81_, v___x_95_);
v___x_97_ = l_Lean_Syntax_node1(v___x_72_, v___x_80_, v___x_96_);
v___x_98_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__27));
v___x_99_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_72_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
lean_inc_ref(v___x_99_);
lean_inc_ref(v___x_84_);
v___x_100_ = l_Lean_Syntax_node3(v___x_72_, v___x_82_, v___x_84_, v___x_97_, v___x_99_);
v___x_101_ = l_Lean_Syntax_node1(v___x_72_, v___x_76_, v___x_100_);
v___x_102_ = l_Lean_Syntax_node1(v___x_72_, v___x_81_, v___x_101_);
v___x_103_ = l_Lean_Syntax_node1(v___x_72_, v___x_80_, v___x_102_);
lean_inc_ref(v___x_79_);
v___x_104_ = l_Lean_Syntax_node2(v___x_72_, v___x_77_, v___x_79_, v___x_103_);
v___x_105_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__31));
v___x_106_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___closed__32));
v___x_107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_72_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_Syntax_node1(v___x_72_, v___x_105_, v___x_107_);
v___x_109_ = l_Lean_Syntax_node3(v___x_72_, v___x_76_, v___x_108_, v___x_90_, v___x_94_);
v___x_110_ = l_Lean_Syntax_node1(v___x_72_, v___x_81_, v___x_109_);
v___x_111_ = l_Lean_Syntax_node1(v___x_72_, v___x_80_, v___x_110_);
v___x_112_ = l_Lean_Syntax_node3(v___x_72_, v___x_82_, v___x_84_, v___x_111_, v___x_99_);
v___x_113_ = l_Lean_Syntax_node1(v___x_72_, v___x_76_, v___x_112_);
v___x_114_ = l_Lean_Syntax_node1(v___x_72_, v___x_81_, v___x_113_);
v___x_115_ = l_Lean_Syntax_node1(v___x_72_, v___x_80_, v___x_114_);
v___x_116_ = l_Lean_Syntax_node2(v___x_72_, v___x_77_, v___x_79_, v___x_115_);
v___x_117_ = l_Lean_Syntax_node2(v___x_72_, v___x_76_, v___x_104_, v___x_116_);
v___x_118_ = l_Lean_Syntax_node2(v___x_72_, v___x_74_, v___x_75_, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_65_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1___boxed(lean_object* v_x_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lp_kanon__tiny__values_Tiny_Lib___aux__Tiny__Lib__Rule______macroRules__tacticKanon__auto__1(v_x_120_, v_a_121_, v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_123_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Lib_Int(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Lib_Rule(uint8_t builtin) {
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
res = initialize_kanon__tiny__values_Tiny_Lib_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
