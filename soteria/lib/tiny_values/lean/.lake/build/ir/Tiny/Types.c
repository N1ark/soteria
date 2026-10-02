// Lean compiler output
// Module: Tiny.Types
// Imports: public import Init public meta import Init
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Unop_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Unop_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqUnop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqUnop___boxed(lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Tiny.Unop.Not"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__0_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__1_value;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_kanon__tiny__values_Tiny_instReprUnop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_instReprUnop_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_instReprUnop___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprUnop___closed__0_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_instReprUnop = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprUnop___closed__0_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instInhabitedUnop_default;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instInhabitedUnop;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Binop_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqBinop(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqBinop___boxed(lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Tiny.Binop.And"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__0_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Tiny.Binop.Or"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__2_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__3_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Tiny.Binop.Eq"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__4_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__4_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__5 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__5_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Tiny.Binop.Leq"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__6 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__6_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__6_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__7 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__7_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Tiny.Binop.Lt"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__8 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__8_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__8_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__9 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__9_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Tiny.Binop.Plus"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__10 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__10_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__10_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__11 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__11_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Tiny.Binop.Minus"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__12 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__12_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__12_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__13 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__13_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Tiny.Binop.Times"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__14 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__14_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__14_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__15 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__15_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Tiny.Binop.Div"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__16 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__16_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__16_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__17 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__17_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Tiny.Binop.Rem"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__18 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__18_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__18_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__19 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__19_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Tiny.Binop.Mod"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__20 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__20_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__20_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__21 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__21_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_kanon__tiny__values_Tiny_instReprBinop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_instReprBinop_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop___closed__0_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_instReprBinop = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprBinop___closed__0_value;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instInhabitedBinop_default;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instInhabitedBinop;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Nop_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Nop_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqNop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqNop___boxed(lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Tiny.Nop.Distinct"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__0_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_kanon__tiny__values_Tiny_instReprNop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_instReprNop_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_instReprNop___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprNop___closed__0_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_instReprNop = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprNop___closed__0_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instInhabitedNop_default;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instInhabitedNop;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Ty_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqTy(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqTy___boxed(lean_object*, lean_object*);
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Tiny.Ty.TBool"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__0_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__1_value;
static const lean_string_object lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Tiny.Ty.TInt"};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__2_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__2_value)}};
static const lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__3_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_kanon__tiny__values_Tiny_instReprTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_instReprTy_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_instReprTy___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy___closed__0_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_instReprTy = (const lean_object*)&lp_kanon__tiny__values_Tiny_instReprTy___closed__0_value;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instInhabitedTy_default;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instInhabitedTy;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Unop_ofNat(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Unop_ofNat___boxed(lean_object* v_n_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_kanon__tiny__values_Tiny_Unop_ofNat(v_n_3_);
lean_dec(v_n_3_);
return v_res_4_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqUnop(lean_object* v_x_5_, lean_object* v_y_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqUnop___boxed(lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_kanon__tiny__values_Tiny_instDecidableEqUnop(v_x_8_, v_y_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(2u);
v___x_16_ = lean_nat_to_int(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_to_int(v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg(lean_object* v_prec_19_){
_start:
{
lean_object* v___y_21_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1024u);
v___x_28_ = lean_nat_dec_le(v___x_27_, v_prec_19_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
v___x_29_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_21_ = v___x_29_;
goto v___jp_20_;
}
else
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_21_ = v___x_30_;
goto v___jp_20_;
}
v___jp_20_:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__1));
lean_inc(v___y_21_);
v___x_23_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_23_, 0, v___y_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
v___x_24_ = 0;
v___x_25_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_25_, 0, v___x_23_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*1, v___x_24_);
v___x_26_ = l_Repr_addAppParen(v___x_25_, v_prec_19_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___boxed(lean_object* v_prec_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg(v_prec_31_);
lean_dec(v_prec_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr(lean_object* v_x_33_, lean_object* v_prec_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg(v_prec_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprUnop_repr___boxed(lean_object* v_x_36_, lean_object* v_prec_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_kanon__tiny__values_Tiny_instReprUnop_repr(v_x_36_, v_prec_37_);
lean_dec(v_prec_37_);
return v_res_38_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedUnop_default(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedUnop(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorIdx(uint8_t v_x_43_){
_start:
{
switch(v_x_43_)
{
case 0:
{
lean_object* v___x_44_; 
v___x_44_ = lean_unsigned_to_nat(0u);
return v___x_44_;
}
case 1:
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(1u);
return v___x_45_;
}
case 2:
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(2u);
return v___x_46_;
}
case 3:
{
lean_object* v___x_47_; 
v___x_47_ = lean_unsigned_to_nat(3u);
return v___x_47_;
}
case 4:
{
lean_object* v___x_48_; 
v___x_48_ = lean_unsigned_to_nat(4u);
return v___x_48_;
}
case 5:
{
lean_object* v___x_49_; 
v___x_49_ = lean_unsigned_to_nat(5u);
return v___x_49_;
}
case 6:
{
lean_object* v___x_50_; 
v___x_50_ = lean_unsigned_to_nat(6u);
return v___x_50_;
}
case 7:
{
lean_object* v___x_51_; 
v___x_51_ = lean_unsigned_to_nat(7u);
return v___x_51_;
}
case 8:
{
lean_object* v___x_52_; 
v___x_52_ = lean_unsigned_to_nat(8u);
return v___x_52_;
}
case 9:
{
lean_object* v___x_53_; 
v___x_53_ = lean_unsigned_to_nat(9u);
return v___x_53_;
}
default: 
{
lean_object* v___x_54_; 
v___x_54_ = lean_unsigned_to_nat(10u);
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorIdx___boxed(lean_object* v_x_55_){
_start:
{
uint8_t v_x_boxed_56_; lean_object* v_res_57_; 
v_x_boxed_56_ = lean_unbox(v_x_55_);
v_res_57_ = lp_kanon__tiny__values_Tiny_Binop_ctorIdx(v_x_boxed_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim___redArg(lean_object* v_k_58_){
_start:
{
lean_inc(v_k_58_);
return v_k_58_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim___redArg___boxed(lean_object* v_k_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_kanon__tiny__values_Tiny_Binop_ctorElim___redArg(v_k_59_);
lean_dec(v_k_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim(lean_object* v_motive_61_, lean_object* v_ctorIdx_62_, uint8_t v_t_63_, lean_object* v_h_64_, lean_object* v_k_65_){
_start:
{
lean_inc(v_k_65_);
return v_k_65_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ctorElim___boxed(lean_object* v_motive_66_, lean_object* v_ctorIdx_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_k_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = lp_kanon__tiny__values_Tiny_Binop_ctorElim(v_motive_66_, v_ctorIdx_67_, v_t_boxed_71_, v_h_69_, v_k_70_);
lean_dec(v_k_70_);
lean_dec(v_ctorIdx_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim___redArg(lean_object* v_And_73_){
_start:
{
lean_inc(v_And_73_);
return v_And_73_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim___redArg___boxed(lean_object* v_And_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = lp_kanon__tiny__values_Tiny_Binop_And_elim___redArg(v_And_74_);
lean_dec(v_And_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim(lean_object* v_motive_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_And_79_){
_start:
{
lean_inc(v_And_79_);
return v_And_79_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_And_elim___boxed(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_And_83_){
_start:
{
uint8_t v_t_boxed_84_; lean_object* v_res_85_; 
v_t_boxed_84_ = lean_unbox(v_t_81_);
v_res_85_ = lp_kanon__tiny__values_Tiny_Binop_And_elim(v_motive_80_, v_t_boxed_84_, v_h_82_, v_And_83_);
lean_dec(v_And_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim___redArg(lean_object* v_Or_86_){
_start:
{
lean_inc(v_Or_86_);
return v_Or_86_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim___redArg___boxed(lean_object* v_Or_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_kanon__tiny__values_Tiny_Binop_Or_elim___redArg(v_Or_87_);
lean_dec(v_Or_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim(lean_object* v_motive_89_, uint8_t v_t_90_, lean_object* v_h_91_, lean_object* v_Or_92_){
_start:
{
lean_inc(v_Or_92_);
return v_Or_92_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Or_elim___boxed(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_Or_96_){
_start:
{
uint8_t v_t_boxed_97_; lean_object* v_res_98_; 
v_t_boxed_97_ = lean_unbox(v_t_94_);
v_res_98_ = lp_kanon__tiny__values_Tiny_Binop_Or_elim(v_motive_93_, v_t_boxed_97_, v_h_95_, v_Or_96_);
lean_dec(v_Or_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim___redArg(lean_object* v_Eq_99_){
_start:
{
lean_inc(v_Eq_99_);
return v_Eq_99_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim___redArg___boxed(lean_object* v_Eq_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_kanon__tiny__values_Tiny_Binop_Eq_elim___redArg(v_Eq_100_);
lean_dec(v_Eq_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim(lean_object* v_motive_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_Eq_105_){
_start:
{
lean_inc(v_Eq_105_);
return v_Eq_105_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Eq_elim___boxed(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_Eq_109_){
_start:
{
uint8_t v_t_boxed_110_; lean_object* v_res_111_; 
v_t_boxed_110_ = lean_unbox(v_t_107_);
v_res_111_ = lp_kanon__tiny__values_Tiny_Binop_Eq_elim(v_motive_106_, v_t_boxed_110_, v_h_108_, v_Eq_109_);
lean_dec(v_Eq_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim___redArg(lean_object* v_Leq_112_){
_start:
{
lean_inc(v_Leq_112_);
return v_Leq_112_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim___redArg___boxed(lean_object* v_Leq_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_kanon__tiny__values_Tiny_Binop_Leq_elim___redArg(v_Leq_113_);
lean_dec(v_Leq_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim(lean_object* v_motive_115_, uint8_t v_t_116_, lean_object* v_h_117_, lean_object* v_Leq_118_){
_start:
{
lean_inc(v_Leq_118_);
return v_Leq_118_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Leq_elim___boxed(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_Leq_122_){
_start:
{
uint8_t v_t_boxed_123_; lean_object* v_res_124_; 
v_t_boxed_123_ = lean_unbox(v_t_120_);
v_res_124_ = lp_kanon__tiny__values_Tiny_Binop_Leq_elim(v_motive_119_, v_t_boxed_123_, v_h_121_, v_Leq_122_);
lean_dec(v_Leq_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim___redArg(lean_object* v_Lt_125_){
_start:
{
lean_inc(v_Lt_125_);
return v_Lt_125_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim___redArg___boxed(lean_object* v_Lt_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_kanon__tiny__values_Tiny_Binop_Lt_elim___redArg(v_Lt_126_);
lean_dec(v_Lt_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim(lean_object* v_motive_128_, uint8_t v_t_129_, lean_object* v_h_130_, lean_object* v_Lt_131_){
_start:
{
lean_inc(v_Lt_131_);
return v_Lt_131_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Lt_elim___boxed(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_Lt_135_){
_start:
{
uint8_t v_t_boxed_136_; lean_object* v_res_137_; 
v_t_boxed_136_ = lean_unbox(v_t_133_);
v_res_137_ = lp_kanon__tiny__values_Tiny_Binop_Lt_elim(v_motive_132_, v_t_boxed_136_, v_h_134_, v_Lt_135_);
lean_dec(v_Lt_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim___redArg(lean_object* v_Plus_138_){
_start:
{
lean_inc(v_Plus_138_);
return v_Plus_138_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim___redArg___boxed(lean_object* v_Plus_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_kanon__tiny__values_Tiny_Binop_Plus_elim___redArg(v_Plus_139_);
lean_dec(v_Plus_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim(lean_object* v_motive_141_, uint8_t v_t_142_, lean_object* v_h_143_, lean_object* v_Plus_144_){
_start:
{
lean_inc(v_Plus_144_);
return v_Plus_144_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Plus_elim___boxed(lean_object* v_motive_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_Plus_148_){
_start:
{
uint8_t v_t_boxed_149_; lean_object* v_res_150_; 
v_t_boxed_149_ = lean_unbox(v_t_146_);
v_res_150_ = lp_kanon__tiny__values_Tiny_Binop_Plus_elim(v_motive_145_, v_t_boxed_149_, v_h_147_, v_Plus_148_);
lean_dec(v_Plus_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim___redArg(lean_object* v_Minus_151_){
_start:
{
lean_inc(v_Minus_151_);
return v_Minus_151_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim___redArg___boxed(lean_object* v_Minus_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_kanon__tiny__values_Tiny_Binop_Minus_elim___redArg(v_Minus_152_);
lean_dec(v_Minus_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim(lean_object* v_motive_154_, uint8_t v_t_155_, lean_object* v_h_156_, lean_object* v_Minus_157_){
_start:
{
lean_inc(v_Minus_157_);
return v_Minus_157_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Minus_elim___boxed(lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_Minus_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = lp_kanon__tiny__values_Tiny_Binop_Minus_elim(v_motive_158_, v_t_boxed_162_, v_h_160_, v_Minus_161_);
lean_dec(v_Minus_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim___redArg(lean_object* v_Times_164_){
_start:
{
lean_inc(v_Times_164_);
return v_Times_164_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim___redArg___boxed(lean_object* v_Times_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = lp_kanon__tiny__values_Tiny_Binop_Times_elim___redArg(v_Times_165_);
lean_dec(v_Times_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_Times_170_){
_start:
{
lean_inc(v_Times_170_);
return v_Times_170_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Times_elim___boxed(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_Times_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = lp_kanon__tiny__values_Tiny_Binop_Times_elim(v_motive_171_, v_t_boxed_175_, v_h_173_, v_Times_174_);
lean_dec(v_Times_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim___redArg(lean_object* v_Div_177_){
_start:
{
lean_inc(v_Div_177_);
return v_Div_177_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim___redArg___boxed(lean_object* v_Div_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lp_kanon__tiny__values_Tiny_Binop_Div_elim___redArg(v_Div_178_);
lean_dec(v_Div_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_Div_183_){
_start:
{
lean_inc(v_Div_183_);
return v_Div_183_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Div_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_Div_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = lp_kanon__tiny__values_Tiny_Binop_Div_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_Div_187_);
lean_dec(v_Div_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim___redArg(lean_object* v_Rem_190_){
_start:
{
lean_inc(v_Rem_190_);
return v_Rem_190_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim___redArg___boxed(lean_object* v_Rem_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = lp_kanon__tiny__values_Tiny_Binop_Rem_elim___redArg(v_Rem_191_);
lean_dec(v_Rem_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim(lean_object* v_motive_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_Rem_196_){
_start:
{
lean_inc(v_Rem_196_);
return v_Rem_196_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Rem_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_Rem_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = lp_kanon__tiny__values_Tiny_Binop_Rem_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_Rem_200_);
lean_dec(v_Rem_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim___redArg(lean_object* v_Mod_203_){
_start:
{
lean_inc(v_Mod_203_);
return v_Mod_203_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim___redArg___boxed(lean_object* v_Mod_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = lp_kanon__tiny__values_Tiny_Binop_Mod_elim___redArg(v_Mod_204_);
lean_dec(v_Mod_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_Mod_209_){
_start:
{
lean_inc(v_Mod_209_);
return v_Mod_209_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_Mod_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_Mod_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = lp_kanon__tiny__values_Tiny_Binop_Mod_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_Mod_213_);
lean_dec(v_Mod_213_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Binop_ofNat(lean_object* v_n_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = lean_nat_dec_le(v_n_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(7u);
v___x_220_ = lean_nat_dec_le(v_n_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(8u);
v___x_222_ = lean_nat_dec_le(v_n_216_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(9u);
v___x_224_ = lean_nat_dec_le(v_n_216_, v___x_223_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; 
v___x_225_ = 10;
return v___x_225_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 9;
return v___x_226_;
}
}
else
{
uint8_t v___x_227_; 
v___x_227_ = 8;
return v___x_227_;
}
}
else
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(5u);
v___x_229_ = lean_nat_dec_le(v_n_216_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(6u);
v___x_231_ = lean_nat_dec_le(v_n_216_, v___x_230_);
if (v___x_231_ == 0)
{
uint8_t v___x_232_; 
v___x_232_ = 7;
return v___x_232_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 6;
return v___x_233_;
}
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 5;
return v___x_234_;
}
}
}
else
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_dec_le(v_n_216_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(2u);
v___x_238_ = lean_nat_dec_le(v_n_216_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = lean_nat_dec_le(v_n_216_, v___x_239_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
v___x_241_ = 4;
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 3;
return v___x_242_;
}
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 2;
return v___x_243_;
}
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_le(v_n_216_, v___x_244_);
if (v___x_245_ == 0)
{
uint8_t v___x_246_; 
v___x_246_ = 1;
return v___x_246_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Binop_ofNat___boxed(lean_object* v_n_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = lp_kanon__tiny__values_Tiny_Binop_ofNat(v_n_248_);
lean_dec(v_n_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqBinop(uint8_t v_x_251_, uint8_t v_y_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_253_ = lp_kanon__tiny__values_Tiny_Binop_ctorIdx(v_x_251_);
v___x_254_ = lp_kanon__tiny__values_Tiny_Binop_ctorIdx(v_y_252_);
v___x_255_ = lean_nat_dec_eq(v___x_253_, v___x_254_);
lean_dec(v___x_254_);
lean_dec(v___x_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqBinop___boxed(lean_object* v_x_256_, lean_object* v_y_257_){
_start:
{
uint8_t v_x_13__boxed_258_; uint8_t v_y_14__boxed_259_; uint8_t v_res_260_; lean_object* v_r_261_; 
v_x_13__boxed_258_ = lean_unbox(v_x_256_);
v_y_14__boxed_259_ = lean_unbox(v_y_257_);
v_res_260_ = lp_kanon__tiny__values_Tiny_instDecidableEqBinop(v_x_13__boxed_258_, v_y_14__boxed_259_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr(uint8_t v_x_295_, lean_object* v_prec_296_){
_start:
{
lean_object* v___y_298_; lean_object* v___y_305_; lean_object* v___y_312_; lean_object* v___y_319_; lean_object* v___y_326_; lean_object* v___y_333_; lean_object* v___y_340_; lean_object* v___y_347_; lean_object* v___y_354_; lean_object* v___y_361_; lean_object* v___y_368_; 
switch(v_x_295_)
{
case 0:
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(1024u);
v___x_375_ = lean_nat_dec_le(v___x_374_, v_prec_296_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_298_ = v___x_376_;
goto v___jp_297_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_298_ = v___x_377_;
goto v___jp_297_;
}
}
case 1:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(1024u);
v___x_379_ = lean_nat_dec_le(v___x_378_, v_prec_296_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_305_ = v___x_380_;
goto v___jp_304_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_305_ = v___x_381_;
goto v___jp_304_;
}
}
case 2:
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1024u);
v___x_383_ = lean_nat_dec_le(v___x_382_, v_prec_296_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_312_ = v___x_384_;
goto v___jp_311_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_312_ = v___x_385_;
goto v___jp_311_;
}
}
case 3:
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(1024u);
v___x_387_ = lean_nat_dec_le(v___x_386_, v_prec_296_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_319_ = v___x_388_;
goto v___jp_318_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_319_ = v___x_389_;
goto v___jp_318_;
}
}
case 4:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(1024u);
v___x_391_ = lean_nat_dec_le(v___x_390_, v_prec_296_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_326_ = v___x_392_;
goto v___jp_325_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_326_ = v___x_393_;
goto v___jp_325_;
}
}
case 5:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1024u);
v___x_395_ = lean_nat_dec_le(v___x_394_, v_prec_296_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_333_ = v___x_396_;
goto v___jp_332_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_333_ = v___x_397_;
goto v___jp_332_;
}
}
case 6:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1024u);
v___x_399_ = lean_nat_dec_le(v___x_398_, v_prec_296_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_340_ = v___x_400_;
goto v___jp_339_;
}
else
{
lean_object* v___x_401_; 
v___x_401_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_340_ = v___x_401_;
goto v___jp_339_;
}
}
case 7:
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_unsigned_to_nat(1024u);
v___x_403_ = lean_nat_dec_le(v___x_402_, v_prec_296_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_347_ = v___x_404_;
goto v___jp_346_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_347_ = v___x_405_;
goto v___jp_346_;
}
}
case 8:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(1024u);
v___x_407_ = lean_nat_dec_le(v___x_406_, v_prec_296_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_354_ = v___x_408_;
goto v___jp_353_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_354_ = v___x_409_;
goto v___jp_353_;
}
}
case 9:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(1024u);
v___x_411_ = lean_nat_dec_le(v___x_410_, v_prec_296_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_361_ = v___x_412_;
goto v___jp_360_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_361_ = v___x_413_;
goto v___jp_360_;
}
}
default: 
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(1024u);
v___x_415_ = lean_nat_dec_le(v___x_414_, v_prec_296_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_368_ = v___x_416_;
goto v___jp_367_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_368_ = v___x_417_;
goto v___jp_367_;
}
}
}
v___jp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_299_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__1));
lean_inc(v___y_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___y_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = 0;
v___x_302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_301_);
v___x_303_ = l_Repr_addAppParen(v___x_302_, v_prec_296_);
return v___x_303_;
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_306_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__3));
lean_inc(v___y_305_);
v___x_307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = 0;
v___x_309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_308_);
v___x_310_ = l_Repr_addAppParen(v___x_309_, v_prec_296_);
return v___x_310_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_313_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__5));
lean_inc(v___y_312_);
v___x_314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_314_, 0, v___y_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = 0;
v___x_316_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_315_);
v___x_317_ = l_Repr_addAppParen(v___x_316_, v_prec_296_);
return v___x_317_;
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_320_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__7));
lean_inc(v___y_319_);
v___x_321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = 0;
v___x_323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_322_);
v___x_324_ = l_Repr_addAppParen(v___x_323_, v_prec_296_);
return v___x_324_;
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_327_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__9));
lean_inc(v___y_326_);
v___x_328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_328_, 0, v___y_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = 0;
v___x_330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*1, v___x_329_);
v___x_331_ = l_Repr_addAppParen(v___x_330_, v_prec_296_);
return v___x_331_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_334_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__11));
lean_inc(v___y_333_);
v___x_335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_335_, 0, v___y_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = 0;
v___x_337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_336_);
v___x_338_ = l_Repr_addAppParen(v___x_337_, v_prec_296_);
return v___x_338_;
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_341_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__13));
lean_inc(v___y_340_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___y_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = 0;
v___x_344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_343_);
v___x_345_ = l_Repr_addAppParen(v___x_344_, v_prec_296_);
return v___x_345_;
}
v___jp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_348_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__15));
lean_inc(v___y_347_);
v___x_349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_349_, 0, v___y_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = 0;
v___x_351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*1, v___x_350_);
v___x_352_ = l_Repr_addAppParen(v___x_351_, v_prec_296_);
return v___x_352_;
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__17));
lean_inc(v___y_354_);
v___x_356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_356_, 0, v___y_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = 0;
v___x_358_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*1, v___x_357_);
v___x_359_ = l_Repr_addAppParen(v___x_358_, v_prec_296_);
return v___x_359_;
}
v___jp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_362_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__19));
lean_inc(v___y_361_);
v___x_363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_363_, 0, v___y_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = 0;
v___x_365_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_364_);
v___x_366_ = l_Repr_addAppParen(v___x_365_, v_prec_296_);
return v___x_366_;
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_369_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprBinop_repr___closed__21));
lean_inc(v___y_368_);
v___x_370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_370_, 0, v___y_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = 0;
v___x_372_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*1, v___x_371_);
v___x_373_ = l_Repr_addAppParen(v___x_372_, v_prec_296_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprBinop_repr___boxed(lean_object* v_x_418_, lean_object* v_prec_419_){
_start:
{
uint8_t v_x_621__boxed_420_; lean_object* v_res_421_; 
v_x_621__boxed_420_ = lean_unbox(v_x_418_);
v_res_421_ = lp_kanon__tiny__values_Tiny_instReprBinop_repr(v_x_621__boxed_420_, v_prec_419_);
lean_dec(v_prec_419_);
return v_res_421_;
}
}
static uint8_t _init_lp_kanon__tiny__values_Tiny_instInhabitedBinop_default(void){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
static uint8_t _init_lp_kanon__tiny__values_Tiny_instInhabitedBinop(void){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Nop_ofNat(lean_object* v_n_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_box(0);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Nop_ofNat___boxed(lean_object* v_n_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = lp_kanon__tiny__values_Tiny_Nop_ofNat(v_n_428_);
lean_dec(v_n_428_);
return v_res_429_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqNop(lean_object* v_x_430_, lean_object* v_y_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = 1;
return v___x_432_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqNop___boxed(lean_object* v_x_433_, lean_object* v_y_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = lp_kanon__tiny__values_Tiny_instDecidableEqNop(v_x_433_, v_y_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg(lean_object* v_prec_440_){
_start:
{
lean_object* v___y_442_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(1024u);
v___x_449_ = lean_nat_dec_le(v___x_448_, v_prec_440_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_442_ = v___x_450_;
goto v___jp_441_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_442_ = v___x_451_;
goto v___jp_441_;
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_443_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___closed__1));
lean_inc(v___y_442_);
v___x_444_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_444_, 0, v___y_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = 0;
v___x_446_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*1, v___x_445_);
v___x_447_ = l_Repr_addAppParen(v___x_446_, v_prec_440_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg___boxed(lean_object* v_prec_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg(v_prec_452_);
lean_dec(v_prec_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr(lean_object* v_x_454_, lean_object* v_prec_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lp_kanon__tiny__values_Tiny_instReprNop_repr___redArg(v_prec_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprNop_repr___boxed(lean_object* v_x_457_, lean_object* v_prec_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = lp_kanon__tiny__values_Tiny_instReprNop_repr(v_x_457_, v_prec_458_);
lean_dec(v_prec_458_);
return v_res_459_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedNop_default(void){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedNop(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorIdx(uint8_t v_x_464_){
_start:
{
if (v_x_464_ == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_unsigned_to_nat(0u);
return v___x_465_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = lean_unsigned_to_nat(1u);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorIdx___boxed(lean_object* v_x_467_){
_start:
{
uint8_t v_x_boxed_468_; lean_object* v_res_469_; 
v_x_boxed_468_ = lean_unbox(v_x_467_);
v_res_469_ = lp_kanon__tiny__values_Tiny_Ty_ctorIdx(v_x_boxed_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim___redArg(lean_object* v_k_470_){
_start:
{
lean_inc(v_k_470_);
return v_k_470_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim___redArg___boxed(lean_object* v_k_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = lp_kanon__tiny__values_Tiny_Ty_ctorElim___redArg(v_k_471_);
lean_dec(v_k_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim(lean_object* v_motive_473_, lean_object* v_ctorIdx_474_, uint8_t v_t_475_, lean_object* v_h_476_, lean_object* v_k_477_){
_start:
{
lean_inc(v_k_477_);
return v_k_477_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ctorElim___boxed(lean_object* v_motive_478_, lean_object* v_ctorIdx_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_k_482_){
_start:
{
uint8_t v_t_boxed_483_; lean_object* v_res_484_; 
v_t_boxed_483_ = lean_unbox(v_t_480_);
v_res_484_ = lp_kanon__tiny__values_Tiny_Ty_ctorElim(v_motive_478_, v_ctorIdx_479_, v_t_boxed_483_, v_h_481_, v_k_482_);
lean_dec(v_k_482_);
lean_dec(v_ctorIdx_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim___redArg(lean_object* v_TBool_485_){
_start:
{
lean_inc(v_TBool_485_);
return v_TBool_485_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim___redArg___boxed(lean_object* v_TBool_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = lp_kanon__tiny__values_Tiny_Ty_TBool_elim___redArg(v_TBool_486_);
lean_dec(v_TBool_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim(lean_object* v_motive_488_, uint8_t v_t_489_, lean_object* v_h_490_, lean_object* v_TBool_491_){
_start:
{
lean_inc(v_TBool_491_);
return v_TBool_491_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TBool_elim___boxed(lean_object* v_motive_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_TBool_495_){
_start:
{
uint8_t v_t_boxed_496_; lean_object* v_res_497_; 
v_t_boxed_496_ = lean_unbox(v_t_493_);
v_res_497_ = lp_kanon__tiny__values_Tiny_Ty_TBool_elim(v_motive_492_, v_t_boxed_496_, v_h_494_, v_TBool_495_);
lean_dec(v_TBool_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim___redArg(lean_object* v_TInt_498_){
_start:
{
lean_inc(v_TInt_498_);
return v_TInt_498_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim___redArg___boxed(lean_object* v_TInt_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = lp_kanon__tiny__values_Tiny_Ty_TInt_elim___redArg(v_TInt_499_);
lean_dec(v_TInt_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim(lean_object* v_motive_501_, uint8_t v_t_502_, lean_object* v_h_503_, lean_object* v_TInt_504_){
_start:
{
lean_inc(v_TInt_504_);
return v_TInt_504_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_TInt_elim___boxed(lean_object* v_motive_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_TInt_508_){
_start:
{
uint8_t v_t_boxed_509_; lean_object* v_res_510_; 
v_t_boxed_509_ = lean_unbox(v_t_506_);
v_res_510_ = lp_kanon__tiny__values_Tiny_Ty_TInt_elim(v_motive_505_, v_t_boxed_509_, v_h_507_, v_TInt_508_);
lean_dec(v_TInt_508_);
return v_res_510_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Ty_ofNat(lean_object* v_n_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_nat_dec_le(v_n_511_, v___x_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 1;
return v___x_514_;
}
else
{
uint8_t v___x_515_; 
v___x_515_ = 0;
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Ty_ofNat___boxed(lean_object* v_n_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = lp_kanon__tiny__values_Tiny_Ty_ofNat(v_n_516_);
lean_dec(v_n_516_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqTy(uint8_t v_x_519_, uint8_t v_y_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lp_kanon__tiny__values_Tiny_Ty_ctorIdx(v_x_519_);
v___x_522_ = lp_kanon__tiny__values_Tiny_Ty_ctorIdx(v_y_520_);
v___x_523_ = lean_nat_dec_eq(v___x_521_, v___x_522_);
lean_dec(v___x_522_);
lean_dec(v___x_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqTy___boxed(lean_object* v_x_524_, lean_object* v_y_525_){
_start:
{
uint8_t v_x_13__boxed_526_; uint8_t v_y_14__boxed_527_; uint8_t v_res_528_; lean_object* v_r_529_; 
v_x_13__boxed_526_ = lean_unbox(v_x_524_);
v_y_14__boxed_527_ = lean_unbox(v_y_525_);
v_res_528_ = lp_kanon__tiny__values_Tiny_instDecidableEqTy(v_x_13__boxed_526_, v_y_14__boxed_527_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr(uint8_t v_x_536_, lean_object* v_prec_537_){
_start:
{
lean_object* v___y_539_; lean_object* v___y_546_; 
if (v_x_536_ == 0)
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(1024u);
v___x_553_ = lean_nat_dec_le(v___x_552_, v_prec_537_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_539_ = v___x_554_;
goto v___jp_538_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_539_ = v___x_555_;
goto v___jp_538_;
}
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(1024u);
v___x_557_ = lean_nat_dec_le(v___x_556_, v_prec_537_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__2);
v___y_546_ = v___x_558_;
goto v___jp_545_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3, &lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3_once, _init_lp_kanon__tiny__values_Tiny_instReprUnop_repr___redArg___closed__3);
v___y_546_ = v___x_559_;
goto v___jp_545_;
}
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_540_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__1));
lean_inc(v___y_539_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___y_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = 0;
v___x_543_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*1, v___x_542_);
v___x_544_ = l_Repr_addAppParen(v___x_543_, v_prec_537_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_instReprTy_repr___closed__3));
lean_inc(v___y_546_);
v___x_548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = 0;
v___x_550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*1, v___x_549_);
v___x_551_ = l_Repr_addAppParen(v___x_550_, v_prec_537_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instReprTy_repr___boxed(lean_object* v_x_560_, lean_object* v_prec_561_){
_start:
{
uint8_t v_x_117__boxed_562_; lean_object* v_res_563_; 
v_x_117__boxed_562_ = lean_unbox(v_x_560_);
v_res_563_ = lp_kanon__tiny__values_Tiny_instReprTy_repr(v_x_117__boxed_562_, v_prec_561_);
lean_dec(v_prec_561_);
return v_res_563_;
}
}
static uint8_t _init_lp_kanon__tiny__values_Tiny_instInhabitedTy_default(void){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = 0;
return v___x_566_;
}
}
static uint8_t _init_lp_kanon__tiny__values_Tiny_instInhabitedTy(void){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = 0;
return v___x_567_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_kanon__tiny__values_Tiny_instInhabitedUnop_default = _init_lp_kanon__tiny__values_Tiny_instInhabitedUnop_default();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_instInhabitedUnop_default);
lp_kanon__tiny__values_Tiny_instInhabitedUnop = _init_lp_kanon__tiny__values_Tiny_instInhabitedUnop();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_instInhabitedUnop);
lp_kanon__tiny__values_Tiny_instInhabitedBinop_default = _init_lp_kanon__tiny__values_Tiny_instInhabitedBinop_default();
lp_kanon__tiny__values_Tiny_instInhabitedBinop = _init_lp_kanon__tiny__values_Tiny_instInhabitedBinop();
lp_kanon__tiny__values_Tiny_instInhabitedNop_default = _init_lp_kanon__tiny__values_Tiny_instInhabitedNop_default();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_instInhabitedNop_default);
lp_kanon__tiny__values_Tiny_instInhabitedNop = _init_lp_kanon__tiny__values_Tiny_instInhabitedNop();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_instInhabitedNop);
lp_kanon__tiny__values_Tiny_instInhabitedTy_default = _init_lp_kanon__tiny__values_Tiny_instInhabitedTy_default();
lp_kanon__tiny__values_Tiny_instInhabitedTy = _init_lp_kanon__tiny__values_Tiny_instInhabitedTy();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
