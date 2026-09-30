// Lean compiler output
// Module: Tiny.Model
// Imports: public import Init public meta import Init public import Tiny.Signatures
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
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lp_kanon__tiny__values_Tiny_int__z(lean_object*);
lean_object* lp_kanon_Kanon_whenSome___redArg(uint8_t, lean_object*);
extern lean_object* lp_kanon__tiny__values_Tiny_v__false;
lean_object* lp_kanon_Kanon_firstSome___redArg(lean_object*);
extern lean_object* lp_kanon__tiny__values_Tiny_v__true;
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_kanon__tiny__values_Tiny_zero;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqTy(uint8_t, uint8_t);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_of__bool(uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_of__bool___boxed(lean_object*);
static const lean_ctor_object lp_kanon__tiny__values_Tiny_sure__neq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_sure__neq___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_sure__neq___closed__0_value;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_sure__neq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sure__neq___boxed(lean_object*, lean_object*);
static const lean_ctor_object lp_kanon__tiny__values_Tiny_at__most__one___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_kanon__tiny__values_Tiny_at__most__one___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_at__most__one___closed__0_value;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_at__most__one(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_at__most__one___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_at__most__one_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_at__most__one_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check__one_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check__one_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_abs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_abs___closed__0;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_abs(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_abs___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_is__mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_is__mod___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_is__mod___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_is__mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__10_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mk__commut__binop(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mk__commut__binop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_spec(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_spec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_spec(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_spec(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_spec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_spec(lean_object*, lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false__(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__true___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__true__(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__true___00__boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true___00__redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true__(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true___00__boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__false___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__false__(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__false___00__boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true__(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true___00__boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___closed__0;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false__(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__not___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__not(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__not___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__or__(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__and__(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__ite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__distinct(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__lt___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__leq___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__leq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__leq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__default___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__default___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true___00__redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true___00__boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false___00__redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false___00__boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__not__bool(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__not__bool___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__then(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__then___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__then(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__then___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__else(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__else___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__else(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__else___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__not__guard(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__default___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__default(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__default___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__false__(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__true___00__redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__true__(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__true___00__boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__nots(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__add__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__sub__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__mul__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__typed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__zero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__zero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__zero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__assoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__left(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__left___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__right(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__right___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__left__sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__left__sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__right__sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__right__sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__default___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__one___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__one(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__default___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_step___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__default___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__mod__mod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__add__mod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__default___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__add__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__add__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__sub__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__sub__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__rsub__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__rsub__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__rsub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__rsub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mul__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mul__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__ite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__ite__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__default___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__add__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__add__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__sub__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__sub__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__rsub__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__rsub__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rsub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rsub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mul__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mul__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__ite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__ite__const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__default___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__default___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_b__and_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__0_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_b__or_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__1_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_b__not_spec, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__2 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__2_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_b__ite_spec, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__3 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__3_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_sem__eq_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__4 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__4_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_sem__eq__untyped_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__5 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__5_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_b__distinct_spec, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__6 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__6_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_add_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__7 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__7_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_sub_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__8 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__8_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_mul_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__9 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__9_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_div_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__10 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__10_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_rem_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__11 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__11_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_mod___00spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__12 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__12_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_neg_spec, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__13 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__13_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_lt_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__14 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__14_value;
static const lean_closure_object lp_kanon__tiny__values_Tiny_opsRaw___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_kanon__tiny__values_Tiny_leq_spec, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_kanon__tiny__values_Tiny_opsRaw___closed__15 = (const lean_object*)&lp_kanon__tiny__values_Tiny_opsRaw___closed__15_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_opsRaw(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_of__bool(uint8_t v_b_1_){
_start:
{
if (v_b_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lp_kanon__tiny__values_Tiny_v__false;
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lp_kanon__tiny__values_Tiny_v__true;
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_of__bool___boxed(lean_object* v_b_4_){
_start:
{
uint8_t v_b_boxed_5_; lean_object* v_res_6_; 
v_b_boxed_5_ = lean_unbox(v_b_4_);
v_res_6_ = lp_kanon__tiny__values_Tiny_of__bool(v_b_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_sure__neq(lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v___y_13_; lean_object* v___y_14_; lean_object* v_kind_22_; uint8_t v_ty_23_; lean_object* v_kind_24_; uint8_t v_ty_25_; uint8_t v___x_26_; lean_object* v___y_28_; uint8_t v___y_47_; 
v_kind_22_ = lean_ctor_get(v_a_10_, 0);
v_ty_23_ = lean_ctor_get_uint8(v_a_10_, sizeof(void*)*1);
v_kind_24_ = lean_ctor_get(v_b_11_, 0);
lean_inc_ref(v_kind_24_);
v_ty_25_ = lean_ctor_get_uint8(v_b_11_, sizeof(void*)*1);
lean_dec_ref(v_b_11_);
v___x_26_ = lp_kanon__tiny__values_Tiny_instDecidableEqTy(v_ty_23_, v_ty_25_);
if (v___x_26_ == 0)
{
uint8_t v___x_49_; 
lean_dec_ref(v_kind_24_);
v___x_49_ = 1;
return v___x_49_;
}
else
{
if (lean_obj_tag(v_kind_22_) == 4)
{
if (lean_obj_tag(v_kind_24_) == 4)
{
uint8_t v_a_50_; 
v_a_50_ = lean_ctor_get_uint8(v_kind_22_, 0);
if (v_a_50_ == 0)
{
uint8_t v_a_51_; 
v_a_51_ = lean_ctor_get_uint8(v_kind_24_, 0);
if (v_a_51_ == 0)
{
v___y_47_ = v___x_26_;
goto v___jp_46_;
}
else
{
goto v___jp_43_;
}
}
else
{
uint8_t v_a_52_; 
v_a_52_ = lean_ctor_get_uint8(v_kind_24_, 0);
v___y_47_ = v_a_52_;
goto v___jp_46_;
}
}
else
{
lean_object* v___x_53_; 
v___x_53_ = lean_box(0);
v___y_28_ = v___x_53_;
goto v___jp_27_;
}
}
else
{
lean_object* v___x_54_; 
v___x_54_ = lean_box(0);
v___y_28_ = v___x_54_;
goto v___jp_27_;
}
}
v___jp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_15_ = lean_box(0);
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___y_14_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___y_13_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
v___x_18_ = lp_kanon_Kanon_firstSome___redArg(v___x_17_);
lean_dec_ref_known(v___x_17_, 2);
if (lean_obj_tag(v___x_18_) == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 0;
return v___x_19_;
}
else
{
lean_object* v_val_20_; uint8_t v___x_21_; 
v_val_20_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v___x_18_, 1);
v___x_21_ = lean_unbox(v_val_20_);
lean_dec(v_val_20_);
return v___x_21_;
}
}
v___jp_27_:
{
if (lean_obj_tag(v_kind_22_) == 6)
{
if (lean_obj_tag(v_kind_24_) == 6)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_40_; 
v_a_29_ = lean_ctor_get(v_kind_22_, 0);
v_a_30_ = lean_ctor_get(v_kind_24_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v_kind_24_);
if (v_isSharedCheck_40_ == 0)
{
v___x_32_ = v_kind_24_;
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v_kind_24_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
uint8_t v___x_34_; 
v___x_34_ = lean_int_dec_eq(v_a_29_, v_a_30_);
lean_dec(v_a_30_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_box(v___x_26_);
if (v_isShared_33_ == 0)
{
lean_ctor_set_tag(v___x_32_, 1);
lean_ctor_set(v___x_32_, 0, v___x_35_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
v___y_13_ = v___y_28_;
v___y_14_ = v___x_37_;
goto v___jp_12_;
}
}
else
{
lean_object* v___x_39_; 
lean_del_object(v___x_32_);
v___x_39_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_sure__neq___closed__0));
v___y_13_ = v___y_28_;
v___y_14_ = v___x_39_;
goto v___jp_12_;
}
}
}
else
{
lean_object* v___x_41_; 
lean_dec_ref(v_kind_24_);
v___x_41_ = lean_box(0);
v___y_13_ = v___y_28_;
v___y_14_ = v___x_41_;
goto v___jp_12_;
}
}
else
{
lean_object* v___x_42_; 
lean_dec_ref(v_kind_24_);
v___x_42_ = lean_box(0);
v___y_13_ = v___y_28_;
v___y_14_ = v___x_42_;
goto v___jp_12_;
}
}
v___jp_43_:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_box(v___x_26_);
v___x_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
v___y_28_ = v___x_45_;
goto v___jp_27_;
}
v___jp_46_:
{
if (v___y_47_ == 0)
{
goto v___jp_43_;
}
else
{
lean_object* v___x_48_; 
v___x_48_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_sure__neq___closed__0));
v___y_28_ = v___x_48_;
goto v___jp_27_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sure__neq___boxed(lean_object* v_a_55_, lean_object* v_b_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = lp_kanon__tiny__values_Tiny_sure__neq(v_a_55_, v_b_56_);
lean_dec_ref(v_a_55_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_at__most__one(lean_object* v_l_62_){
_start:
{
lean_object* v___y_64_; lean_object* v___y_65_; lean_object* v___y_74_; 
if (lean_obj_tag(v_l_62_) == 0)
{
lean_object* v___x_79_; 
v___x_79_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_at__most__one___closed__0));
v___y_74_ = v___x_79_;
goto v___jp_73_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
v___y_74_ = v___x_80_;
goto v___jp_73_;
}
v___jp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_box(0);
lean_inc(v___y_65_);
v___x_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
lean_inc(v___y_64_);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_64_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lp_kanon_Kanon_firstSome___redArg(v___x_68_);
lean_dec_ref_known(v___x_68_, 2);
if (lean_obj_tag(v___x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
else
{
lean_object* v_val_71_; uint8_t v___x_72_; 
v_val_71_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_val_71_);
lean_dec_ref_known(v___x_69_, 1);
v___x_72_ = lean_unbox(v_val_71_);
lean_dec(v_val_71_);
return v___x_72_;
}
}
v___jp_73_:
{
if (lean_obj_tag(v_l_62_) == 1)
{
lean_object* v_tail_75_; 
v_tail_75_ = lean_ctor_get(v_l_62_, 1);
if (lean_obj_tag(v_tail_75_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_at__most__one___closed__0));
v___y_64_ = v___y_74_;
v___y_65_ = v___x_76_;
goto v___jp_63_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
v___y_64_ = v___y_74_;
v___y_65_ = v___x_77_;
goto v___jp_63_;
}
}
else
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
v___y_64_ = v___y_74_;
v___y_65_ = v___x_78_;
goto v___jp_63_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_at__most__one___boxed(lean_object* v_l_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = lp_kanon__tiny__values_Tiny_at__most__one(v_l_81_);
lean_dec(v_l_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_at__most__one_match__1_splitter___redArg(lean_object* v_l_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
if (lean_obj_tag(v_l_84_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_h__2_86_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_apply_1(v_h__1_85_, v___x_87_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; 
lean_dec(v_h__1_85_);
v___x_89_ = lean_apply_2(v_h__2_86_, v_l_84_, lean_box(0));
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_at__most__one_match__1_splitter(lean_object* v_motive_90_, lean_object* v_l_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
if (lean_obj_tag(v_l_91_) == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_93_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__1_92_, v___x_94_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; 
lean_dec(v_h__1_92_);
v___x_96_ = lean_apply_2(v_h__2_93_, v_l_91_, lean_box(0));
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check__one_match__1_splitter___redArg(lean_object* v_rest_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
if (lean_obj_tag(v_rest_97_) == 1)
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_99_);
v_head_100_ = lean_ctor_get(v_rest_97_, 0);
lean_inc(v_head_100_);
v_tail_101_ = lean_ctor_get(v_rest_97_, 1);
lean_inc(v_tail_101_);
lean_dec_ref_known(v_rest_97_, 2);
v___x_102_ = lean_apply_2(v_h__1_98_, v_head_100_, v_tail_101_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
lean_dec(v_h__1_98_);
v___x_103_ = lean_apply_2(v_h__2_99_, v_rest_97_, lean_box(0));
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check__one_match__1_splitter(lean_object* v_motive_104_, lean_object* v_rest_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_rest_105_) == 1)
{
lean_object* v_head_108_; lean_object* v_tail_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_107_);
v_head_108_ = lean_ctor_get(v_rest_105_, 0);
lean_inc(v_head_108_);
v_tail_109_ = lean_ctor_get(v_rest_105_, 1);
lean_inc(v_tail_109_);
lean_dec_ref_known(v_rest_105_, 2);
v___x_110_ = lean_apply_2(v_h__1_106_, v_head_108_, v_tail_109_);
return v___x_110_;
}
else
{
lean_object* v___x_111_; 
lean_dec(v_h__1_106_);
v___x_111_ = lean_apply_2(v_h__2_107_, v_rest_105_, lean_box(0));
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check_match__1_splitter___redArg(lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
if (lean_obj_tag(v_x_112_) == 1)
{
lean_object* v_val_115_; uint8_t v___x_116_; 
v_val_115_ = lean_ctor_get(v_x_112_, 0);
v___x_116_ = lean_unbox(v_val_115_);
if (v___x_116_ == 1)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec_ref_known(v_x_112_, 1);
lean_dec(v_h__2_114_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__1_113_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_h__1_113_);
v___x_119_ = lean_apply_2(v_h__2_114_, v_x_112_, lean_box(0));
return v___x_119_;
}
}
else
{
lean_object* v___x_120_; 
lean_dec(v_h__1_113_);
v___x_120_ = lean_apply_2(v_h__2_114_, v_x_112_, lean_box(0));
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_distinct__check_match__1_splitter(lean_object* v_motive_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
if (lean_obj_tag(v_x_122_) == 1)
{
lean_object* v_val_125_; uint8_t v___x_126_; 
v_val_125_ = lean_ctor_get(v_x_122_, 0);
v___x_126_ = lean_unbox(v_val_125_);
if (v___x_126_ == 1)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref_known(v_x_122_, 1);
lean_dec(v_h__2_124_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_apply_1(v_h__1_123_, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
lean_dec(v_h__1_123_);
v___x_129_ = lean_apply_2(v_h__2_124_, v_x_122_, lean_box(0));
return v___x_129_;
}
}
else
{
lean_object* v___x_130_; 
lean_dec(v_h__1_123_);
v___x_130_ = lean_apply_2(v_h__2_124_, v_x_122_, lean_box(0));
return v___x_130_;
}
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_abs___closed__0(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_abs(lean_object* v_z_133_){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_135_ = lean_int_dec_lt(v_z_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_inc(v_z_133_);
return v_z_133_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_int_neg(v_z_133_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_abs___boxed(lean_object* v_z_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_kanon__tiny__values_Tiny_abs(v_z_137_);
lean_dec(v_z_137_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_is__mod(lean_object* v_v_139_, lean_object* v_n_140_){
_start:
{
lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; lean_object* v___y_145_; lean_object* v_kind_155_; uint8_t v_ty_156_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_182_; 
v_kind_155_ = lean_ctor_get(v_v_139_, 0);
v_ty_156_ = lean_ctor_get_uint8(v_v_139_, sizeof(void*)*1);
if (lean_obj_tag(v_kind_155_) == 6)
{
lean_object* v_a_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_a_189_ = lean_ctor_get(v_kind_155_, 0);
v___x_190_ = lean_int_mod(v_a_189_, v_n_140_);
v___x_191_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_192_ = lean_int_dec_eq(v___x_190_, v___x_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(v___x_192_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
v___y_182_ = v___x_194_;
goto v___jp_181_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
v___y_182_ = v___x_195_;
goto v___jp_181_;
}
v___jp_141_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___y_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___y_144_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___y_142_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_150_, 0, v___y_143_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = lp_kanon_Kanon_firstSome___redArg(v___x_150_);
lean_dec_ref_known(v___x_150_, 2);
if (lean_obj_tag(v___x_151_) == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
else
{
lean_object* v_val_153_; uint8_t v___x_154_; 
v_val_153_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_val_153_);
lean_dec_ref_known(v___x_151_, 1);
v___x_154_ = lean_unbox(v_val_153_);
lean_dec(v_val_153_);
return v___x_154_;
}
}
v___jp_157_:
{
if (lean_obj_tag(v_kind_155_) == 2)
{
uint8_t v_a_161_; 
v_a_161_ = lean_ctor_get_uint8(v_kind_155_, sizeof(void*)*2);
if (v_a_161_ == 7)
{
lean_object* v_a_162_; lean_object* v_a_163_; uint8_t v___x_164_; 
v_a_162_ = lean_ctor_get(v_kind_155_, 0);
v_a_163_ = lean_ctor_get(v_kind_155_, 1);
v___x_164_ = lp_kanon__tiny__values_Tiny_is__mod(v_a_162_, v_n_140_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lp_kanon__tiny__values_Tiny_is__mod(v_a_163_, v_n_140_);
v___x_166_ = lean_box(v___x_165_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
v___y_142_ = v___y_158_;
v___y_143_ = v___y_159_;
v___y_144_ = v___y_160_;
v___y_145_ = v___x_167_;
goto v___jp_141_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_box(v___x_164_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___y_142_ = v___y_158_;
v___y_143_ = v___y_159_;
v___y_144_ = v___y_160_;
v___y_145_ = v___x_169_;
goto v___jp_141_;
}
}
else
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
v___y_142_ = v___y_158_;
v___y_143_ = v___y_159_;
v___y_144_ = v___y_160_;
v___y_145_ = v___x_170_;
goto v___jp_141_;
}
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
v___y_142_ = v___y_158_;
v___y_143_ = v___y_159_;
v___y_144_ = v___y_160_;
v___y_145_ = v___x_171_;
goto v___jp_141_;
}
}
v___jp_172_:
{
if (lean_obj_tag(v_kind_155_) == 2)
{
uint8_t v_a_175_; 
v_a_175_ = lean_ctor_get_uint8(v_kind_155_, sizeof(void*)*2);
if (v_a_175_ == 6)
{
lean_object* v_a_176_; lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_176_ = lean_ctor_get(v_kind_155_, 0);
v_a_177_ = lean_ctor_get(v_kind_155_, 1);
v___x_178_ = lp_kanon__tiny__values_Tiny_is__mod___lam__0(v_n_140_, v_a_176_, v_a_177_, v_ty_156_);
v___y_158_ = v___y_174_;
v___y_159_ = v___y_173_;
v___y_160_ = v___x_178_;
goto v___jp_157_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_box(0);
v___y_158_ = v___y_174_;
v___y_159_ = v___y_173_;
v___y_160_ = v___x_179_;
goto v___jp_157_;
}
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
v___y_158_ = v___y_174_;
v___y_159_ = v___y_173_;
v___y_160_ = v___x_180_;
goto v___jp_157_;
}
}
v___jp_181_:
{
if (lean_obj_tag(v_kind_155_) == 2)
{
uint8_t v_a_183_; 
v_a_183_ = lean_ctor_get_uint8(v_kind_155_, sizeof(void*)*2);
if (v_a_183_ == 5)
{
lean_object* v_a_184_; lean_object* v_a_185_; lean_object* v___x_186_; 
v_a_184_ = lean_ctor_get(v_kind_155_, 0);
v_a_185_ = lean_ctor_get(v_kind_155_, 1);
v___x_186_ = lp_kanon__tiny__values_Tiny_is__mod___lam__0(v_n_140_, v_a_184_, v_a_185_, v_ty_156_);
v___y_173_ = v___y_182_;
v___y_174_ = v___x_186_;
goto v___jp_172_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
v___y_173_ = v___y_182_;
v___y_174_ = v___x_187_;
goto v___jp_172_;
}
}
else
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
v___y_173_ = v___y_182_;
v___y_174_ = v___x_188_;
goto v___jp_172_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_is__mod___lam__0(lean_object* v_n_196_, lean_object* v_a_197_, lean_object* v_b_198_, uint8_t v_ty_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lp_kanon__tiny__values_Tiny_is__mod(v_a_197_, v_n_196_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_box(v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
else
{
uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lp_kanon__tiny__values_Tiny_is__mod(v_b_198_, v_n_196_);
v___x_204_ = lean_box(v___x_203_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_is__mod___lam__0___boxed(lean_object* v_n_206_, lean_object* v_a_207_, lean_object* v_b_208_, lean_object* v_ty_209_){
_start:
{
uint8_t v_ty_258__boxed_210_; lean_object* v_res_211_; 
v_ty_258__boxed_210_ = lean_unbox(v_ty_209_);
v_res_211_ = lp_kanon__tiny__values_Tiny_is__mod___lam__0(v_n_206_, v_a_207_, v_b_208_, v_ty_258__boxed_210_);
lean_dec_ref(v_b_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_n_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_is__mod___boxed(lean_object* v_v_212_, lean_object* v_n_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = lp_kanon__tiny__values_Tiny_is__mod(v_v_212_, v_n_213_);
lean_dec(v_n_213_);
lean_dec_ref(v_v_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__1_splitter___redArg(lean_object* v_v_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
lean_object* v_kind_219_; 
v_kind_219_ = lean_ctor_get(v_v_216_, 0);
if (lean_obj_tag(v_kind_219_) == 6)
{
uint8_t v_ty_220_; lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_inc_ref(v_kind_219_);
lean_dec(v_h__2_218_);
v_ty_220_ = lean_ctor_get_uint8(v_v_216_, sizeof(void*)*1);
lean_dec_ref(v_v_216_);
v_a_221_ = lean_ctor_get(v_kind_219_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v_kind_219_, 1);
v___x_222_ = lean_box(v_ty_220_);
v___x_223_ = lean_apply_2(v_h__1_217_, v_a_221_, v___x_222_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; 
lean_dec(v_h__1_217_);
v___x_224_ = lean_apply_2(v_h__2_218_, v_v_216_, lean_box(0));
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__1_splitter(lean_object* v_motive_225_, lean_object* v_v_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
lean_object* v_kind_229_; 
v_kind_229_ = lean_ctor_get(v_v_226_, 0);
if (lean_obj_tag(v_kind_229_) == 6)
{
uint8_t v_ty_230_; lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_inc_ref(v_kind_229_);
lean_dec(v_h__2_228_);
v_ty_230_ = lean_ctor_get_uint8(v_v_226_, sizeof(void*)*1);
lean_dec_ref(v_v_226_);
v_a_231_ = lean_ctor_get(v_kind_229_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v_kind_229_, 1);
v___x_232_ = lean_box(v_ty_230_);
v___x_233_ = lean_apply_2(v_h__1_227_, v_a_231_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
lean_dec(v_h__1_227_);
v___x_234_ = lean_apply_2(v_h__2_228_, v_v_226_, lean_box(0));
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__3_splitter___redArg(lean_object* v_v_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
lean_object* v_kind_238_; 
v_kind_238_ = lean_ctor_get(v_v_235_, 0);
if (lean_obj_tag(v_kind_238_) == 2)
{
uint8_t v_a_239_; 
v_a_239_ = lean_ctor_get_uint8(v_kind_238_, sizeof(void*)*2);
if (v_a_239_ == 5)
{
uint8_t v_ty_240_; lean_object* v_a_241_; lean_object* v_a_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_inc_ref(v_kind_238_);
lean_dec(v_h__2_237_);
v_ty_240_ = lean_ctor_get_uint8(v_v_235_, sizeof(void*)*1);
lean_dec_ref(v_v_235_);
v_a_241_ = lean_ctor_get(v_kind_238_, 0);
lean_inc_ref(v_a_241_);
v_a_242_ = lean_ctor_get(v_kind_238_, 1);
lean_inc_ref(v_a_242_);
lean_dec_ref_known(v_kind_238_, 2);
v___x_243_ = lean_box(v_ty_240_);
v___x_244_ = lean_apply_3(v_h__1_236_, v_a_241_, v_a_242_, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; 
lean_dec(v_h__1_236_);
v___x_245_ = lean_apply_2(v_h__2_237_, v_v_235_, lean_box(0));
return v___x_245_;
}
}
else
{
lean_object* v___x_246_; 
lean_dec(v_h__1_236_);
v___x_246_ = lean_apply_2(v_h__2_237_, v_v_235_, lean_box(0));
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__3_splitter(lean_object* v_motive_247_, lean_object* v_v_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_){
_start:
{
lean_object* v_kind_251_; 
v_kind_251_ = lean_ctor_get(v_v_248_, 0);
if (lean_obj_tag(v_kind_251_) == 2)
{
uint8_t v_a_252_; 
v_a_252_ = lean_ctor_get_uint8(v_kind_251_, sizeof(void*)*2);
if (v_a_252_ == 5)
{
uint8_t v_ty_253_; lean_object* v_a_254_; lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_inc_ref(v_kind_251_);
lean_dec(v_h__2_250_);
v_ty_253_ = lean_ctor_get_uint8(v_v_248_, sizeof(void*)*1);
lean_dec_ref(v_v_248_);
v_a_254_ = lean_ctor_get(v_kind_251_, 0);
lean_inc_ref(v_a_254_);
v_a_255_ = lean_ctor_get(v_kind_251_, 1);
lean_inc_ref(v_a_255_);
lean_dec_ref_known(v_kind_251_, 2);
v___x_256_ = lean_box(v_ty_253_);
v___x_257_ = lean_apply_3(v_h__1_249_, v_a_254_, v_a_255_, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v_h__1_249_);
v___x_258_ = lean_apply_2(v_h__2_250_, v_v_248_, lean_box(0));
return v___x_258_;
}
}
else
{
lean_object* v___x_259_; 
lean_dec(v_h__1_249_);
v___x_259_ = lean_apply_2(v_h__2_250_, v_v_248_, lean_box(0));
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__7_splitter___redArg(lean_object* v_v_260_, lean_object* v_h__1_261_, lean_object* v_h__2_262_){
_start:
{
lean_object* v_kind_263_; 
v_kind_263_ = lean_ctor_get(v_v_260_, 0);
if (lean_obj_tag(v_kind_263_) == 2)
{
uint8_t v_a_264_; 
v_a_264_ = lean_ctor_get_uint8(v_kind_263_, sizeof(void*)*2);
if (v_a_264_ == 6)
{
uint8_t v_ty_265_; lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_inc_ref(v_kind_263_);
lean_dec(v_h__2_262_);
v_ty_265_ = lean_ctor_get_uint8(v_v_260_, sizeof(void*)*1);
lean_dec_ref(v_v_260_);
v_a_266_ = lean_ctor_get(v_kind_263_, 0);
lean_inc_ref(v_a_266_);
v_a_267_ = lean_ctor_get(v_kind_263_, 1);
lean_inc_ref(v_a_267_);
lean_dec_ref_known(v_kind_263_, 2);
v___x_268_ = lean_box(v_ty_265_);
v___x_269_ = lean_apply_3(v_h__1_261_, v_a_266_, v_a_267_, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_dec(v_h__1_261_);
v___x_270_ = lean_apply_2(v_h__2_262_, v_v_260_, lean_box(0));
return v___x_270_;
}
}
else
{
lean_object* v___x_271_; 
lean_dec(v_h__1_261_);
v___x_271_ = lean_apply_2(v_h__2_262_, v_v_260_, lean_box(0));
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__7_splitter(lean_object* v_motive_272_, lean_object* v_v_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_){
_start:
{
lean_object* v_kind_276_; 
v_kind_276_ = lean_ctor_get(v_v_273_, 0);
if (lean_obj_tag(v_kind_276_) == 2)
{
uint8_t v_a_277_; 
v_a_277_ = lean_ctor_get_uint8(v_kind_276_, sizeof(void*)*2);
if (v_a_277_ == 6)
{
uint8_t v_ty_278_; lean_object* v_a_279_; lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
lean_inc_ref(v_kind_276_);
lean_dec(v_h__2_275_);
v_ty_278_ = lean_ctor_get_uint8(v_v_273_, sizeof(void*)*1);
lean_dec_ref(v_v_273_);
v_a_279_ = lean_ctor_get(v_kind_276_, 0);
lean_inc_ref(v_a_279_);
v_a_280_ = lean_ctor_get(v_kind_276_, 1);
lean_inc_ref(v_a_280_);
lean_dec_ref_known(v_kind_276_, 2);
v___x_281_ = lean_box(v_ty_278_);
v___x_282_ = lean_apply_3(v_h__1_274_, v_a_279_, v_a_280_, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
lean_dec(v_h__1_274_);
v___x_283_ = lean_apply_2(v_h__2_275_, v_v_273_, lean_box(0));
return v___x_283_;
}
}
else
{
lean_object* v___x_284_; 
lean_dec(v_h__1_274_);
v___x_284_ = lean_apply_2(v_h__2_275_, v_v_273_, lean_box(0));
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__10_splitter___redArg(lean_object* v_v_285_, lean_object* v_h__1_286_, lean_object* v_h__2_287_){
_start:
{
lean_object* v_kind_288_; 
v_kind_288_ = lean_ctor_get(v_v_285_, 0);
if (lean_obj_tag(v_kind_288_) == 2)
{
uint8_t v_a_289_; 
v_a_289_ = lean_ctor_get_uint8(v_kind_288_, sizeof(void*)*2);
if (v_a_289_ == 7)
{
uint8_t v_ty_290_; lean_object* v_a_291_; lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_inc_ref(v_kind_288_);
lean_dec(v_h__2_287_);
v_ty_290_ = lean_ctor_get_uint8(v_v_285_, sizeof(void*)*1);
lean_dec_ref(v_v_285_);
v_a_291_ = lean_ctor_get(v_kind_288_, 0);
lean_inc_ref(v_a_291_);
v_a_292_ = lean_ctor_get(v_kind_288_, 1);
lean_inc_ref(v_a_292_);
lean_dec_ref_known(v_kind_288_, 2);
v___x_293_ = lean_box(v_ty_290_);
v___x_294_ = lean_apply_3(v_h__1_286_, v_a_291_, v_a_292_, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; 
lean_dec(v_h__1_286_);
v___x_295_ = lean_apply_2(v_h__2_287_, v_v_285_, lean_box(0));
return v___x_295_;
}
}
else
{
lean_object* v___x_296_; 
lean_dec(v_h__1_286_);
v___x_296_ = lean_apply_2(v_h__2_287_, v_v_285_, lean_box(0));
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values___private_Tiny_Model_0__Tiny_is__mod_match__10_splitter(lean_object* v_motive_297_, lean_object* v_v_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_){
_start:
{
lean_object* v_kind_301_; 
v_kind_301_ = lean_ctor_get(v_v_298_, 0);
if (lean_obj_tag(v_kind_301_) == 2)
{
uint8_t v_a_302_; 
v_a_302_ = lean_ctor_get_uint8(v_kind_301_, sizeof(void*)*2);
if (v_a_302_ == 7)
{
uint8_t v_ty_303_; lean_object* v_a_304_; lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_inc_ref(v_kind_301_);
lean_dec(v_h__2_300_);
v_ty_303_ = lean_ctor_get_uint8(v_v_298_, sizeof(void*)*1);
lean_dec_ref(v_v_298_);
v_a_304_ = lean_ctor_get(v_kind_301_, 0);
lean_inc_ref(v_a_304_);
v_a_305_ = lean_ctor_get(v_kind_301_, 1);
lean_inc_ref(v_a_305_);
lean_dec_ref_known(v_kind_301_, 2);
v___x_306_ = lean_box(v_ty_303_);
v___x_307_ = lean_apply_3(v_h__1_299_, v_a_304_, v_a_305_, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_h__1_299_);
v___x_308_ = lean_apply_2(v_h__2_300_, v_v_298_, lean_box(0));
return v___x_308_;
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v_h__1_299_);
v___x_309_ = lean_apply_2(v_h__2_300_, v_v_298_, lean_box(0));
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mk__commut__binop(lean_object* v_O_310_, uint8_t v_op_311_, lean_object* v_l_312_, lean_object* v_r_313_){
_start:
{
lean_object* v_orc_314_; lean_object* v_tag__le_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_orc_314_ = lean_ctor_get(v_O_310_, 0);
lean_inc_ref(v_orc_314_);
lean_dec_ref(v_O_310_);
v_tag__le_315_ = lean_ctor_get(v_orc_314_, 0);
lean_inc_ref(v_tag__le_315_);
lean_dec_ref(v_orc_314_);
lean_inc_ref(v_r_313_);
lean_inc_ref(v_l_312_);
v___x_316_ = lean_apply_2(v_tag__le_315_, v_l_312_, v_r_313_);
v___x_317_ = lean_unbox(v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_318_, 0, v_r_313_);
lean_ctor_set(v___x_318_, 1, v_l_312_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*2, v_op_311_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_319_, 0, v_l_312_);
lean_ctor_set(v___x_319_, 1, v_r_313_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*2, v_op_311_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mk__commut__binop___boxed(lean_object* v_O_320_, lean_object* v_op_321_, lean_object* v_l_322_, lean_object* v_r_323_){
_start:
{
uint8_t v_op_boxed_324_; lean_object* v_res_325_; 
v_op_boxed_324_ = lean_unbox(v_op_321_);
v_res_325_ = lp_kanon__tiny__values_Tiny_mk__commut__binop(v_O_320_, v_op_boxed_324_, v_l_322_, v_r_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_spec(lean_object* v_v1_326_, lean_object* v_v2_327_){
_start:
{
uint8_t v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; 
v___x_328_ = 0;
v___x_329_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_329_, 0, v_v1_326_);
lean_ctor_set(v___x_329_, 1, v_v2_327_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*2, v___x_328_);
v___x_330_ = 0;
v___x_331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_spec(lean_object* v_v1_332_, lean_object* v_v2_333_){
_start:
{
uint8_t v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_334_ = 1;
v___x_335_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_335_, 0, v_v1_332_);
lean_ctor_set(v___x_335_, 1, v_v2_333_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*2, v___x_334_);
v___x_336_ = 0;
v___x_337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_spec(lean_object* v_sv_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; 
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_sv_338_);
v___x_341_ = 0;
v___x_342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*1, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_spec(lean_object* v_guard_343_, lean_object* v_if___344_, lean_object* v_else___345_){
_start:
{
uint8_t v_ty_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_ty_346_ = lean_ctor_get_uint8(v_if___344_, sizeof(void*)*1);
v___x_347_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_347_, 0, v_guard_343_);
lean_ctor_set(v___x_347_, 1, v_if___344_);
lean_ctor_set(v___x_347_, 2, v_else___345_);
v___x_348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*1, v_ty_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_spec(lean_object* v_v1_349_, lean_object* v_v2_350_){
_start:
{
uint8_t v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; lean_object* v___x_354_; 
v___x_351_ = 2;
v___x_352_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_352_, 0, v_v1_349_);
lean_ctor_set(v___x_352_, 1, v_v2_350_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*2, v___x_351_);
v___x_353_ = 0;
v___x_354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_spec(lean_object* v_v1_355_, lean_object* v_v2_356_){
_start:
{
uint8_t v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_357_ = 2;
v___x_358_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_358_, 0, v_v1_355_);
lean_ctor_set(v___x_358_, 1, v_v2_356_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*2, v___x_357_);
v___x_359_ = 0;
v___x_360_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*1, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_spec(lean_object* v_l_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; 
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_l_361_);
v___x_364_ = 0;
v___x_365_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_spec(lean_object* v_v1_366_, lean_object* v_v2_367_){
_start:
{
uint8_t v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v___x_368_ = 5;
v___x_369_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_369_, 0, v_v1_366_);
lean_ctor_set(v___x_369_, 1, v_v2_367_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*2, v___x_368_);
v___x_370_ = 1;
v___x_371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_spec(lean_object* v_v1_372_, lean_object* v_v2_373_){
_start:
{
uint8_t v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; 
v___x_374_ = 6;
v___x_375_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_375_, 0, v_v1_372_);
lean_ctor_set(v___x_375_, 1, v_v2_373_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*2, v___x_374_);
v___x_376_ = 1;
v___x_377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_spec(lean_object* v_v1_378_, lean_object* v_v2_379_){
_start:
{
uint8_t v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; 
v___x_380_ = 7;
v___x_381_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_381_, 0, v_v1_378_);
lean_ctor_set(v___x_381_, 1, v_v2_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*2, v___x_380_);
v___x_382_ = 1;
v___x_383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*1, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_spec(lean_object* v_v1_384_, lean_object* v_v2_385_){
_start:
{
uint8_t v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v___x_386_ = 8;
v___x_387_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_387_, 0, v_v1_384_);
lean_ctor_set(v___x_387_, 1, v_v2_385_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*2, v___x_386_);
v___x_388_ = 1;
v___x_389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_spec(lean_object* v_v1_390_, lean_object* v_v2_391_){
_start:
{
uint8_t v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; 
v___x_392_ = 9;
v___x_393_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_393_, 0, v_v1_390_);
lean_ctor_set(v___x_393_, 1, v_v2_391_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*2, v___x_392_);
v___x_394_ = 1;
v___x_395_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*1, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00spec(lean_object* v_v1_396_, lean_object* v_v2_397_){
_start:
{
uint8_t v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; 
v___x_398_ = 10;
v___x_399_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_399_, 0, v_v1_396_);
lean_ctor_set(v___x_399_, 1, v_v2_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*2, v___x_398_);
v___x_400_ = 1;
v___x_401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_spec(lean_object* v_v_402_){
_start:
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; 
v___x_403_ = 6;
v___x_404_ = lp_kanon__tiny__values_Tiny_zero;
v___x_405_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_v_402_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*2, v___x_403_);
v___x_406_ = 1;
v___x_407_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*1, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_spec(lean_object* v_v1_408_, lean_object* v_v2_409_){
_start:
{
uint8_t v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; 
v___x_410_ = 4;
v___x_411_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_411_, 0, v_v1_408_);
lean_ctor_set(v___x_411_, 1, v_v2_409_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*2, v___x_410_);
v___x_412_ = 0;
v___x_413_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_spec(lean_object* v_v1_414_, lean_object* v_v2_415_){
_start:
{
uint8_t v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v___x_416_ = 3;
v___x_417_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_417_, 0, v_v1_414_);
lean_ctor_set(v___x_417_, 1, v_v2_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*2, v___x_416_);
v___x_418_ = 0;
v___x_419_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*1, v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0(void){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lp_kanon__tiny__values_Tiny_v__false;
v___x_421_ = 1;
v___x_422_ = lp_kanon_Kanon_whenSome___redArg(v___x_421_, v___x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg(lean_object* v_v1_423_, lean_object* v_v2_424_){
_start:
{
lean_object* v___y_426_; lean_object* v_kind_430_; 
v_kind_430_ = lean_ctor_get(v_v1_423_, 0);
if (lean_obj_tag(v_kind_430_) == 4)
{
uint8_t v_a_431_; 
v_a_431_ = lean_ctor_get_uint8(v_kind_430_, 0);
if (v_a_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0);
if (lean_obj_tag(v___x_432_) == 0)
{
v___y_426_ = v___x_432_;
goto v___jp_425_;
}
else
{
return v___x_432_;
}
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_box(0);
v___y_426_ = v___x_433_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_434_; 
v___x_434_ = lean_box(0);
v___y_426_ = v___x_434_;
goto v___jp_425_;
}
v___jp_425_:
{
lean_object* v_kind_427_; 
v_kind_427_ = lean_ctor_get(v_v2_424_, 0);
if (lean_obj_tag(v_kind_427_) == 4)
{
uint8_t v_a_428_; 
v_a_428_ = lean_ctor_get_uint8(v_kind_427_, 0);
if (v_a_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0);
return v___x_429_;
}
else
{
lean_inc(v___y_426_);
return v___y_426_;
}
}
else
{
lean_inc(v___y_426_);
return v___y_426_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___boxed(lean_object* v_v1_435_, lean_object* v_v2_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg(v_v1_435_, v_v2_436_);
lean_dec_ref(v_v2_436_);
lean_dec_ref(v_v1_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false__(lean_object* v_O_438_, lean_object* v_v1_439_, lean_object* v_v2_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg(v_v1_439_, v_v2_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__false___00__boxed(lean_object* v_O_442_, lean_object* v_v1_443_, lean_object* v_v2_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = lp_kanon__tiny__values_Tiny_b__and_r__false__(v_O_442_, v_v1_443_, v_v2_444_);
lean_dec_ref(v_v2_444_);
lean_dec_ref(v_v1_443_);
lean_dec_ref(v_O_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__true___00__redArg(lean_object* v_v1_446_, lean_object* v_v2_447_){
_start:
{
lean_object* v___y_449_; lean_object* v_kind_453_; 
v_kind_453_ = lean_ctor_get(v_v1_446_, 0);
if (lean_obj_tag(v_kind_453_) == 4)
{
uint8_t v_a_454_; 
v_a_454_ = lean_ctor_get_uint8(v_kind_453_, 0);
if (v_a_454_ == 1)
{
lean_object* v___x_455_; 
lean_inc_ref(v_v2_447_);
v___x_455_ = lp_kanon_Kanon_whenSome___redArg(v_a_454_, v_v2_447_);
if (lean_obj_tag(v___x_455_) == 0)
{
v___y_449_ = v___x_455_;
goto v___jp_448_;
}
else
{
lean_dec_ref(v_v2_447_);
lean_dec_ref(v_v1_446_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
v___y_449_ = v___x_456_;
goto v___jp_448_;
}
}
else
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
v___y_449_ = v___x_457_;
goto v___jp_448_;
}
v___jp_448_:
{
lean_object* v_kind_450_; 
v_kind_450_ = lean_ctor_get(v_v2_447_, 0);
lean_inc_ref(v_kind_450_);
lean_dec_ref(v_v2_447_);
if (lean_obj_tag(v_kind_450_) == 4)
{
uint8_t v_a_451_; 
v_a_451_ = lean_ctor_get_uint8(v_kind_450_, 0);
lean_dec_ref_known(v_kind_450_, 0);
if (v_a_451_ == 1)
{
lean_object* v___x_452_; 
lean_dec(v___y_449_);
v___x_452_ = lp_kanon_Kanon_whenSome___redArg(v_a_451_, v_v1_446_);
return v___x_452_;
}
else
{
lean_dec_ref(v_v1_446_);
return v___y_449_;
}
}
else
{
lean_dec_ref(v_kind_450_);
lean_dec_ref(v_v1_446_);
return v___y_449_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__true__(lean_object* v_O_458_, lean_object* v_v1_459_, lean_object* v_v2_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lp_kanon__tiny__values_Tiny_b__and_r__true___00__redArg(v_v1_459_, v_v2_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__true___00__boxed(lean_object* v_O_462_, lean_object* v_v1_463_, lean_object* v_v2_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = lp_kanon__tiny__values_Tiny_b__and_r__true__(v_O_462_, v_v1_463_, v_v2_464_);
lean_dec_ref(v_O_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__and_r__default(lean_object* v_O_466_, lean_object* v_v1_467_, lean_object* v_v2_468_){
_start:
{
uint8_t v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_469_ = 1;
v___x_470_ = 0;
v___x_471_ = lp_kanon__tiny__values_Tiny_mk__commut__binop(v_O_466_, v___x_470_, v_v1_467_, v_v2_468_);
v___x_472_ = 0;
v___x_473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_472_);
v___x_474_ = lp_kanon_Kanon_whenSome___redArg(v___x_469_, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true___00__redArg(lean_object* v_v1_475_, lean_object* v_v2_476_){
_start:
{
lean_object* v___y_478_; lean_object* v_kind_483_; 
v_kind_483_ = lean_ctor_get(v_v1_475_, 0);
if (lean_obj_tag(v_kind_483_) == 4)
{
uint8_t v_a_484_; 
v_a_484_ = lean_ctor_get_uint8(v_kind_483_, 0);
if (v_a_484_ == 1)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_486_ = lp_kanon_Kanon_whenSome___redArg(v_a_484_, v___x_485_);
if (lean_obj_tag(v___x_486_) == 0)
{
v___y_478_ = v___x_486_;
goto v___jp_477_;
}
else
{
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
v___y_478_ = v___x_487_;
goto v___jp_477_;
}
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_box(0);
v___y_478_ = v___x_488_;
goto v___jp_477_;
}
v___jp_477_:
{
lean_object* v_kind_479_; 
v_kind_479_ = lean_ctor_get(v_v2_476_, 0);
if (lean_obj_tag(v_kind_479_) == 4)
{
uint8_t v_a_480_; 
v_a_480_ = lean_ctor_get_uint8(v_kind_479_, 0);
if (v_a_480_ == 1)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v___y_478_);
v___x_481_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_482_ = lp_kanon_Kanon_whenSome___redArg(v_a_480_, v___x_481_);
return v___x_482_;
}
else
{
return v___y_478_;
}
}
else
{
return v___y_478_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true___00__redArg___boxed(lean_object* v_v1_489_, lean_object* v_v2_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = lp_kanon__tiny__values_Tiny_b__or_r__true___00__redArg(v_v1_489_, v_v2_490_);
lean_dec_ref(v_v2_490_);
lean_dec_ref(v_v1_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true__(lean_object* v_O_492_, lean_object* v_v1_493_, lean_object* v_v2_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lp_kanon__tiny__values_Tiny_b__or_r__true___00__redArg(v_v1_493_, v_v2_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__true___00__boxed(lean_object* v_O_496_, lean_object* v_v1_497_, lean_object* v_v2_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = lp_kanon__tiny__values_Tiny_b__or_r__true__(v_O_496_, v_v1_497_, v_v2_498_);
lean_dec_ref(v_v2_498_);
lean_dec_ref(v_v1_497_);
lean_dec_ref(v_O_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__false___00__redArg(lean_object* v_v1_500_, lean_object* v_v2_501_){
_start:
{
lean_object* v___y_503_; lean_object* v_kind_508_; 
v_kind_508_ = lean_ctor_get(v_v1_500_, 0);
if (lean_obj_tag(v_kind_508_) == 4)
{
uint8_t v_a_509_; 
v_a_509_ = lean_ctor_get_uint8(v_kind_508_, 0);
if (v_a_509_ == 0)
{
uint8_t v___x_510_; lean_object* v___x_511_; 
v___x_510_ = 1;
lean_inc_ref(v_v2_501_);
v___x_511_ = lp_kanon_Kanon_whenSome___redArg(v___x_510_, v_v2_501_);
if (lean_obj_tag(v___x_511_) == 0)
{
v___y_503_ = v___x_511_;
goto v___jp_502_;
}
else
{
lean_dec_ref(v_v2_501_);
lean_dec_ref(v_v1_500_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_box(0);
v___y_503_ = v___x_512_;
goto v___jp_502_;
}
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
v___y_503_ = v___x_513_;
goto v___jp_502_;
}
v___jp_502_:
{
lean_object* v_kind_504_; 
v_kind_504_ = lean_ctor_get(v_v2_501_, 0);
lean_inc_ref(v_kind_504_);
lean_dec_ref(v_v2_501_);
if (lean_obj_tag(v_kind_504_) == 4)
{
uint8_t v_a_505_; 
v_a_505_ = lean_ctor_get_uint8(v_kind_504_, 0);
lean_dec_ref_known(v_kind_504_, 0);
if (v_a_505_ == 0)
{
uint8_t v___x_506_; lean_object* v___x_507_; 
lean_dec(v___y_503_);
v___x_506_ = 1;
v___x_507_ = lp_kanon_Kanon_whenSome___redArg(v___x_506_, v_v1_500_);
return v___x_507_;
}
else
{
lean_dec_ref(v_v1_500_);
return v___y_503_;
}
}
else
{
lean_dec_ref(v_kind_504_);
lean_dec_ref(v_v1_500_);
return v___y_503_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__false__(lean_object* v_O_514_, lean_object* v_v1_515_, lean_object* v_v2_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lp_kanon__tiny__values_Tiny_b__or_r__false___00__redArg(v_v1_515_, v_v2_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__false___00__boxed(lean_object* v_O_518_, lean_object* v_v1_519_, lean_object* v_v2_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = lp_kanon__tiny__values_Tiny_b__or_r__false__(v_O_518_, v_v1_519_, v_v2_520_);
lean_dec_ref(v_O_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__or_r__default(lean_object* v_O_522_, lean_object* v_v1_523_, lean_object* v_v2_524_){
_start:
{
uint8_t v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_525_ = 1;
v___x_526_ = 1;
v___x_527_ = lp_kanon__tiny__values_Tiny_mk__commut__binop(v_O_522_, v___x_526_, v_v1_523_, v_v2_524_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = lp_kanon_Kanon_whenSome___redArg(v___x_525_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg(lean_object* v_sv_531_){
_start:
{
lean_object* v_kind_532_; 
v_kind_532_ = lean_ctor_get(v_sv_531_, 0);
if (lean_obj_tag(v_kind_532_) == 4)
{
uint8_t v_a_533_; 
v_a_533_ = lean_ctor_get_uint8(v_kind_532_, 0);
if (v_a_533_ == 1)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lp_kanon__tiny__values_Tiny_v__false;
v___x_535_ = lp_kanon_Kanon_whenSome___redArg(v_a_533_, v___x_534_);
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(0);
return v___x_536_;
}
}
else
{
lean_object* v___x_537_; 
v___x_537_ = lean_box(0);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg___boxed(lean_object* v_sv_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg(v_sv_538_);
lean_dec_ref(v_sv_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true__(lean_object* v_O_540_, lean_object* v_sv_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg(v_sv_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__true___00__boxed(lean_object* v_O_543_, lean_object* v_sv_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = lp_kanon__tiny__values_Tiny_b__not_r__true__(v_O_543_, v_sv_544_);
lean_dec_ref(v_sv_544_);
lean_dec_ref(v_O_543_);
return v_res_545_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___closed__0(void){
_start:
{
lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_547_ = 1;
v___x_548_ = lp_kanon_Kanon_whenSome___redArg(v___x_547_, v___x_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg(lean_object* v_sv_549_){
_start:
{
lean_object* v_kind_550_; 
v_kind_550_ = lean_ctor_get(v_sv_549_, 0);
if (lean_obj_tag(v_kind_550_) == 4)
{
uint8_t v_a_551_; 
v_a_551_ = lean_ctor_get_uint8(v_kind_550_, 0);
if (v_a_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___closed__0);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
return v___x_553_;
}
}
else
{
lean_object* v___x_554_; 
v___x_554_ = lean_box(0);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg___boxed(lean_object* v_sv_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg(v_sv_555_);
lean_dec_ref(v_sv_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false__(lean_object* v_O_557_, lean_object* v_sv_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg(v_sv_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__false___00__boxed(lean_object* v_O_560_, lean_object* v_sv_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = lp_kanon__tiny__values_Tiny_b__not_r__false__(v_O_560_, v_sv_561_);
lean_dec_ref(v_sv_561_);
lean_dec_ref(v_O_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__not___redArg(lean_object* v_sv_563_){
_start:
{
lean_object* v_kind_564_; 
v_kind_564_ = lean_ctor_get(v_sv_563_, 0);
lean_inc_ref(v_kind_564_);
lean_dec_ref(v_sv_563_);
if (lean_obj_tag(v_kind_564_) == 1)
{
lean_object* v_a_565_; uint8_t v___x_566_; lean_object* v___x_567_; 
v_a_565_ = lean_ctor_get(v_kind_564_, 1);
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v_kind_564_, 2);
v___x_566_ = 1;
v___x_567_ = lp_kanon_Kanon_whenSome___redArg(v___x_566_, v_a_565_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; 
lean_dec_ref(v_kind_564_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__not(lean_object* v_O_569_, lean_object* v_sv_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lp_kanon__tiny__values_Tiny_b__not_r__not___redArg(v_sv_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__not___boxed(lean_object* v_O_572_, lean_object* v_sv_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = lp_kanon__tiny__values_Tiny_b__not_r__not(v_O_572_, v_sv_573_);
lean_dec_ref(v_O_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__or__(lean_object* v_O_575_, lean_object* v_sv_576_){
_start:
{
lean_object* v_kind_577_; 
v_kind_577_ = lean_ctor_get(v_sv_576_, 0);
lean_inc_ref(v_kind_577_);
lean_dec_ref(v_sv_576_);
if (lean_obj_tag(v_kind_577_) == 2)
{
uint8_t v_a_578_; 
v_a_578_ = lean_ctor_get_uint8(v_kind_577_, sizeof(void*)*2);
if (v_a_578_ == 1)
{
lean_object* v_a_579_; lean_object* v_a_580_; lean_object* v_b__and_581_; lean_object* v_b__not_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_579_ = lean_ctor_get(v_kind_577_, 0);
lean_inc_ref(v_a_579_);
v_a_580_ = lean_ctor_get(v_kind_577_, 1);
lean_inc_ref(v_a_580_);
lean_dec_ref_known(v_kind_577_, 2);
v_b__and_581_ = lean_ctor_get(v_O_575_, 1);
lean_inc_ref(v_b__and_581_);
v_b__not_582_ = lean_ctor_get(v_O_575_, 3);
lean_inc_ref_n(v_b__not_582_, 2);
lean_dec_ref(v_O_575_);
v___x_583_ = 1;
v___x_584_ = lean_apply_1(v_b__not_582_, v_a_579_);
v___x_585_ = lean_apply_1(v_b__not_582_, v_a_580_);
v___x_586_ = lean_apply_2(v_b__and_581_, v___x_584_, v___x_585_);
v___x_587_ = lp_kanon_Kanon_whenSome___redArg(v___x_583_, v___x_586_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; 
lean_dec_ref_known(v_kind_577_, 2);
lean_dec_ref(v_O_575_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
}
else
{
lean_object* v___x_589_; 
lean_dec_ref(v_kind_577_);
lean_dec_ref(v_O_575_);
v___x_589_ = lean_box(0);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__and__(lean_object* v_O_590_, lean_object* v_sv_591_){
_start:
{
lean_object* v_kind_592_; 
v_kind_592_ = lean_ctor_get(v_sv_591_, 0);
lean_inc_ref(v_kind_592_);
lean_dec_ref(v_sv_591_);
if (lean_obj_tag(v_kind_592_) == 2)
{
uint8_t v_a_593_; 
v_a_593_ = lean_ctor_get_uint8(v_kind_592_, sizeof(void*)*2);
if (v_a_593_ == 0)
{
lean_object* v_a_594_; lean_object* v_a_595_; lean_object* v_b__or_596_; lean_object* v_b__not_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_a_594_ = lean_ctor_get(v_kind_592_, 0);
lean_inc_ref(v_a_594_);
v_a_595_ = lean_ctor_get(v_kind_592_, 1);
lean_inc_ref(v_a_595_);
lean_dec_ref_known(v_kind_592_, 2);
v_b__or_596_ = lean_ctor_get(v_O_590_, 2);
lean_inc_ref(v_b__or_596_);
v_b__not_597_ = lean_ctor_get(v_O_590_, 3);
lean_inc_ref_n(v_b__not_597_, 2);
lean_dec_ref(v_O_590_);
v___x_598_ = 1;
v___x_599_ = lean_apply_1(v_b__not_597_, v_a_594_);
v___x_600_ = lean_apply_1(v_b__not_597_, v_a_595_);
v___x_601_ = lean_apply_2(v_b__or_596_, v___x_599_, v___x_600_);
v___x_602_ = lp_kanon_Kanon_whenSome___redArg(v___x_598_, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; 
lean_dec_ref_known(v_kind_592_, 2);
lean_dec_ref(v_O_590_);
v___x_603_ = lean_box(0);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; 
lean_dec_ref(v_kind_592_);
lean_dec_ref(v_O_590_);
v___x_604_ = lean_box(0);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__ite(lean_object* v_O_605_, lean_object* v_sv_606_){
_start:
{
lean_object* v_kind_607_; 
v_kind_607_ = lean_ctor_get(v_sv_606_, 0);
lean_inc_ref(v_kind_607_);
lean_dec_ref(v_sv_606_);
if (lean_obj_tag(v_kind_607_) == 5)
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v_a_610_; lean_object* v_b__not_611_; lean_object* v_b__ite_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_a_608_ = lean_ctor_get(v_kind_607_, 0);
lean_inc_ref(v_a_608_);
v_a_609_ = lean_ctor_get(v_kind_607_, 1);
lean_inc_ref(v_a_609_);
v_a_610_ = lean_ctor_get(v_kind_607_, 2);
lean_inc_ref(v_a_610_);
lean_dec_ref_known(v_kind_607_, 3);
v_b__not_611_ = lean_ctor_get(v_O_605_, 3);
lean_inc_ref_n(v_b__not_611_, 2);
v_b__ite_612_ = lean_ctor_get(v_O_605_, 4);
lean_inc_ref(v_b__ite_612_);
lean_dec_ref(v_O_605_);
v___x_613_ = 1;
v___x_614_ = lean_apply_1(v_b__not_611_, v_a_609_);
v___x_615_ = lean_apply_1(v_b__not_611_, v_a_610_);
v___x_616_ = lean_apply_3(v_b__ite_612_, v_a_608_, v___x_614_, v___x_615_);
v___x_617_ = lp_kanon_Kanon_whenSome___redArg(v___x_613_, v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v_kind_607_);
lean_dec_ref(v_O_605_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__distinct(lean_object* v_O_619_, lean_object* v_sv_620_){
_start:
{
lean_object* v_kind_621_; 
v_kind_621_ = lean_ctor_get(v_sv_620_, 0);
lean_inc_ref(v_kind_621_);
lean_dec_ref(v_sv_620_);
if (lean_obj_tag(v_kind_621_) == 3)
{
lean_object* v_a_622_; 
v_a_622_ = lean_ctor_get(v_kind_621_, 1);
lean_inc(v_a_622_);
lean_dec_ref_known(v_kind_621_, 2);
if (lean_obj_tag(v_a_622_) == 1)
{
lean_object* v_tail_623_; 
v_tail_623_ = lean_ctor_get(v_a_622_, 1);
lean_inc(v_tail_623_);
if (lean_obj_tag(v_tail_623_) == 1)
{
lean_object* v_tail_624_; 
v_tail_624_ = lean_ctor_get(v_tail_623_, 1);
if (lean_obj_tag(v_tail_624_) == 0)
{
lean_object* v_head_625_; lean_object* v_head_626_; lean_object* v_sem__eq_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_head_625_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_head_625_);
lean_dec_ref_known(v_a_622_, 2);
v_head_626_ = lean_ctor_get(v_tail_623_, 0);
lean_inc(v_head_626_);
lean_dec_ref_known(v_tail_623_, 2);
v_sem__eq_627_ = lean_ctor_get(v_O_619_, 5);
lean_inc_ref(v_sem__eq_627_);
lean_dec_ref(v_O_619_);
v___x_628_ = 1;
v___x_629_ = lean_apply_2(v_sem__eq_627_, v_head_625_, v_head_626_);
v___x_630_ = lp_kanon_Kanon_whenSome___redArg(v___x_628_, v___x_629_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
lean_dec_ref_known(v_tail_623_, 2);
lean_dec_ref_known(v_a_622_, 2);
lean_dec_ref(v_O_619_);
v___x_631_ = lean_box(0);
return v___x_631_;
}
}
else
{
lean_object* v___x_632_; 
lean_dec(v_tail_623_);
lean_dec_ref_known(v_a_622_, 2);
lean_dec_ref(v_O_619_);
v___x_632_ = lean_box(0);
return v___x_632_;
}
}
else
{
lean_object* v___x_633_; 
lean_dec(v_a_622_);
lean_dec_ref(v_O_619_);
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
else
{
lean_object* v___x_634_; 
lean_dec_ref(v_kind_621_);
lean_dec_ref(v_O_619_);
v___x_634_ = lean_box(0);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__lt___redArg(lean_object* v_sv_635_){
_start:
{
lean_object* v_kind_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_659_; 
v_kind_636_ = lean_ctor_get(v_sv_635_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_sv_635_);
if (v_isSharedCheck_659_ == 0)
{
v___x_638_ = v_sv_635_;
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_kind_636_);
lean_dec(v_sv_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
if (lean_obj_tag(v_kind_636_) == 2)
{
uint8_t v_a_640_; 
v_a_640_ = lean_ctor_get_uint8(v_kind_636_, sizeof(void*)*2);
if (v_a_640_ == 4)
{
lean_object* v_a_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_656_; 
v_a_641_ = lean_ctor_get(v_kind_636_, 0);
v_a_642_ = lean_ctor_get(v_kind_636_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_kind_636_);
if (v_isSharedCheck_656_ == 0)
{
v___x_644_ = v_kind_636_;
v_isShared_645_ = v_isSharedCheck_656_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_inc(v_a_641_);
lean_dec(v_kind_636_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_656_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; uint8_t v___x_647_; lean_object* v___x_649_; 
v___x_646_ = 1;
v___x_647_ = 3;
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v_a_641_);
lean_ctor_set(v___x_644_, 0, v_a_642_);
v___x_649_ = v___x_644_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_642_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_a_641_);
v___x_649_ = v_reuseFailAlloc_655_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
uint8_t v___x_650_; lean_object* v___x_652_; 
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*2, v___x_647_);
v___x_650_ = 0;
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_649_);
v___x_652_ = v___x_638_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_649_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*1, v___x_650_);
v___x_653_ = lp_kanon_Kanon_whenSome___redArg(v___x_646_, v___x_652_);
return v___x_653_;
}
}
}
}
else
{
lean_object* v___x_657_; 
lean_dec_ref_known(v_kind_636_, 2);
lean_del_object(v___x_638_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
}
else
{
lean_object* v___x_658_; 
lean_del_object(v___x_638_);
lean_dec_ref(v_kind_636_);
v___x_658_ = lean_box(0);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__lt(lean_object* v_O_660_, lean_object* v_sv_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lp_kanon__tiny__values_Tiny_b__not_r__lt___redArg(v_sv_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__lt___boxed(lean_object* v_O_663_, lean_object* v_sv_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = lp_kanon__tiny__values_Tiny_b__not_r__lt(v_O_663_, v_sv_664_);
lean_dec_ref(v_O_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__leq___redArg(lean_object* v_sv_666_){
_start:
{
lean_object* v_kind_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_690_; 
v_kind_667_ = lean_ctor_get(v_sv_666_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v_sv_666_);
if (v_isSharedCheck_690_ == 0)
{
v___x_669_ = v_sv_666_;
v_isShared_670_ = v_isSharedCheck_690_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_kind_667_);
lean_dec(v_sv_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_690_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
if (lean_obj_tag(v_kind_667_) == 2)
{
uint8_t v_a_671_; 
v_a_671_ = lean_ctor_get_uint8(v_kind_667_, sizeof(void*)*2);
if (v_a_671_ == 3)
{
lean_object* v_a_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_687_; 
v_a_672_ = lean_ctor_get(v_kind_667_, 0);
v_a_673_ = lean_ctor_get(v_kind_667_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_kind_667_);
if (v_isSharedCheck_687_ == 0)
{
v___x_675_ = v_kind_667_;
v_isShared_676_ = v_isSharedCheck_687_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_inc(v_a_672_);
lean_dec(v_kind_667_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_687_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
uint8_t v___x_677_; uint8_t v___x_678_; lean_object* v___x_680_; 
v___x_677_ = 1;
v___x_678_ = 4;
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_a_672_);
lean_ctor_set(v___x_675_, 0, v_a_673_);
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_672_);
v___x_680_ = v_reuseFailAlloc_686_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
uint8_t v___x_681_; lean_object* v___x_683_; 
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*2, v___x_678_);
v___x_681_ = 0;
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_680_);
v___x_683_ = v___x_669_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_680_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; 
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v___x_681_);
v___x_684_ = lp_kanon_Kanon_whenSome___redArg(v___x_677_, v___x_683_);
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_688_; 
lean_dec_ref_known(v_kind_667_, 2);
lean_del_object(v___x_669_);
v___x_688_ = lean_box(0);
return v___x_688_;
}
}
else
{
lean_object* v___x_689_; 
lean_del_object(v___x_669_);
lean_dec_ref(v_kind_667_);
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__leq(lean_object* v_O_691_, lean_object* v_sv_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lp_kanon__tiny__values_Tiny_b__not_r__leq___redArg(v_sv_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__leq___boxed(lean_object* v_O_694_, lean_object* v_sv_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = lp_kanon__tiny__values_Tiny_b__not_r__leq(v_O_694_, v_sv_695_);
lean_dec_ref(v_O_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__default___redArg(lean_object* v_sv_697_){
_start:
{
uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_698_ = 1;
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_sv_697_);
v___x_701_ = 0;
v___x_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v___x_701_);
v___x_703_ = lp_kanon_Kanon_whenSome___redArg(v___x_698_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__default(lean_object* v_O_704_, lean_object* v_sv_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lp_kanon__tiny__values_Tiny_b__not_r__default___redArg(v_sv_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_r__default___boxed(lean_object* v_O_707_, lean_object* v_sv_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = lp_kanon__tiny__values_Tiny_b__not_r__default(v_O_707_, v_sv_708_);
lean_dec_ref(v_O_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__not_step(lean_object* v_O_710_, lean_object* v_sv_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_712_ = lp_kanon__tiny__values_Tiny_b__not_r__true___00__redArg(v_sv_711_);
v___x_713_ = lp_kanon__tiny__values_Tiny_b__not_r__false___00__redArg(v_sv_711_);
lean_inc_ref_n(v_sv_711_, 8);
v___x_714_ = lp_kanon__tiny__values_Tiny_b__not_r__not___redArg(v_sv_711_);
lean_inc_ref_n(v_O_710_, 3);
v___x_715_ = lp_kanon__tiny__values_Tiny_b__not_r__or__(v_O_710_, v_sv_711_);
v___x_716_ = lp_kanon__tiny__values_Tiny_b__not_r__and__(v_O_710_, v_sv_711_);
v___x_717_ = lp_kanon__tiny__values_Tiny_b__not_r__ite(v_O_710_, v_sv_711_);
v___x_718_ = lp_kanon__tiny__values_Tiny_b__not_r__distinct(v_O_710_, v_sv_711_);
v___x_719_ = lp_kanon__tiny__values_Tiny_b__not_r__lt___redArg(v_sv_711_);
v___x_720_ = lp_kanon__tiny__values_Tiny_b__not_r__leq___redArg(v_sv_711_);
v___x_721_ = lp_kanon__tiny__values_Tiny_b__not_r__default___redArg(v_sv_711_);
v___x_722_ = lean_box(0);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_720_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_719_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_718_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_717_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_716_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_715_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_714_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_713_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_712_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lp_kanon_Kanon_firstSome___redArg(v___x_732_);
lean_dec_ref_known(v___x_732_, 2);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
v___x_734_ = lp_kanon__tiny__values_Tiny_b__not_spec(v_sv_711_);
return v___x_734_;
}
else
{
lean_object* v_val_735_; 
lean_dec_ref(v_sv_711_);
v_val_735_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_733_, 1);
return v_val_735_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true___00__redArg(lean_object* v_guard_736_, lean_object* v_if___737_){
_start:
{
lean_object* v_kind_738_; 
v_kind_738_ = lean_ctor_get(v_guard_736_, 0);
if (lean_obj_tag(v_kind_738_) == 4)
{
uint8_t v_a_739_; 
v_a_739_ = lean_ctor_get_uint8(v_kind_738_, 0);
if (v_a_739_ == 1)
{
lean_object* v___x_740_; 
v___x_740_ = lp_kanon_Kanon_whenSome___redArg(v_a_739_, v_if___737_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; 
lean_dec_ref(v_if___737_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
else
{
lean_object* v___x_742_; 
lean_dec_ref(v_if___737_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true___00__redArg___boxed(lean_object* v_guard_743_, lean_object* v_if___744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = lp_kanon__tiny__values_Tiny_b__ite_r__true___00__redArg(v_guard_743_, v_if___744_);
lean_dec_ref(v_guard_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__(lean_object* v_O_746_, lean_object* v_guard_747_, lean_object* v_if___748_, lean_object* v_else___749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lp_kanon__tiny__values_Tiny_b__ite_r__true___00__redArg(v_guard_747_, v_if___748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true___00__boxed(lean_object* v_O_751_, lean_object* v_guard_752_, lean_object* v_if___753_, lean_object* v_else___754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = lp_kanon__tiny__values_Tiny_b__ite_r__true__(v_O_751_, v_guard_752_, v_if___753_, v_else___754_);
lean_dec_ref(v_else___754_);
lean_dec_ref(v_guard_752_);
lean_dec_ref(v_O_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false___00__redArg(lean_object* v_guard_756_, lean_object* v_else___757_){
_start:
{
lean_object* v_kind_758_; 
v_kind_758_ = lean_ctor_get(v_guard_756_, 0);
if (lean_obj_tag(v_kind_758_) == 4)
{
uint8_t v_a_759_; 
v_a_759_ = lean_ctor_get_uint8(v_kind_758_, 0);
if (v_a_759_ == 0)
{
uint8_t v___x_760_; lean_object* v___x_761_; 
v___x_760_ = 1;
v___x_761_ = lp_kanon_Kanon_whenSome___redArg(v___x_760_, v_else___757_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; 
lean_dec_ref(v_else___757_);
v___x_762_ = lean_box(0);
return v___x_762_;
}
}
else
{
lean_object* v___x_763_; 
lean_dec_ref(v_else___757_);
v___x_763_ = lean_box(0);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false___00__redArg___boxed(lean_object* v_guard_764_, lean_object* v_else___765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = lp_kanon__tiny__values_Tiny_b__ite_r__false___00__redArg(v_guard_764_, v_else___765_);
lean_dec_ref(v_guard_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__(lean_object* v_O_767_, lean_object* v_guard_768_, lean_object* v_if___769_, lean_object* v_else___770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lp_kanon__tiny__values_Tiny_b__ite_r__false___00__redArg(v_guard_768_, v_else___770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false___00__boxed(lean_object* v_O_772_, lean_object* v_guard_773_, lean_object* v_if___774_, lean_object* v_else___775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = lp_kanon__tiny__values_Tiny_b__ite_r__false__(v_O_772_, v_guard_773_, v_if___774_, v_else___775_);
lean_dec_ref(v_if___774_);
lean_dec_ref(v_guard_773_);
lean_dec_ref(v_O_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool___redArg(lean_object* v_guard_777_, lean_object* v_if___778_, lean_object* v_else___779_){
_start:
{
lean_object* v_kind_780_; 
v_kind_780_ = lean_ctor_get(v_if___778_, 0);
if (lean_obj_tag(v_kind_780_) == 4)
{
uint8_t v_a_781_; 
v_a_781_ = lean_ctor_get_uint8(v_kind_780_, 0);
if (v_a_781_ == 1)
{
lean_object* v_kind_782_; 
v_kind_782_ = lean_ctor_get(v_else___779_, 0);
if (lean_obj_tag(v_kind_782_) == 4)
{
uint8_t v_a_783_; 
v_a_783_ = lean_ctor_get_uint8(v_kind_782_, 0);
if (v_a_783_ == 0)
{
lean_object* v___x_784_; 
v___x_784_ = lp_kanon_Kanon_whenSome___redArg(v_a_781_, v_guard_777_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; 
lean_dec_ref(v_guard_777_);
v___x_785_ = lean_box(0);
return v___x_785_;
}
}
else
{
lean_object* v___x_786_; 
lean_dec_ref(v_guard_777_);
v___x_786_ = lean_box(0);
return v___x_786_;
}
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v_guard_777_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
}
else
{
lean_object* v___x_788_; 
lean_dec_ref(v_guard_777_);
v___x_788_ = lean_box(0);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool___redArg___boxed(lean_object* v_guard_789_, lean_object* v_if___790_, lean_object* v_else___791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = lp_kanon__tiny__values_Tiny_b__ite_r__bool___redArg(v_guard_789_, v_if___790_, v_else___791_);
lean_dec_ref(v_else___791_);
lean_dec_ref(v_if___790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool(lean_object* v_O_793_, lean_object* v_guard_794_, lean_object* v_if___795_, lean_object* v_else___796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = lp_kanon__tiny__values_Tiny_b__ite_r__bool___redArg(v_guard_794_, v_if___795_, v_else___796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__bool___boxed(lean_object* v_O_798_, lean_object* v_guard_799_, lean_object* v_if___800_, lean_object* v_else___801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = lp_kanon__tiny__values_Tiny_b__ite_r__bool(v_O_798_, v_guard_799_, v_if___800_, v_else___801_);
lean_dec_ref(v_else___801_);
lean_dec_ref(v_if___800_);
lean_dec_ref(v_O_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__not__bool(lean_object* v_O_803_, lean_object* v_guard_804_, lean_object* v_if___805_, lean_object* v_else___806_){
_start:
{
lean_object* v_kind_807_; 
v_kind_807_ = lean_ctor_get(v_if___805_, 0);
if (lean_obj_tag(v_kind_807_) == 4)
{
uint8_t v_a_808_; 
v_a_808_ = lean_ctor_get_uint8(v_kind_807_, 0);
if (v_a_808_ == 0)
{
lean_object* v_kind_809_; 
v_kind_809_ = lean_ctor_get(v_else___806_, 0);
if (lean_obj_tag(v_kind_809_) == 4)
{
uint8_t v_a_810_; 
v_a_810_ = lean_ctor_get_uint8(v_kind_809_, 0);
if (v_a_810_ == 1)
{
lean_object* v_b__not_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_b__not_811_ = lean_ctor_get(v_O_803_, 3);
lean_inc_ref(v_b__not_811_);
lean_dec_ref(v_O_803_);
v___x_812_ = lean_apply_1(v_b__not_811_, v_guard_804_);
v___x_813_ = lp_kanon_Kanon_whenSome___redArg(v_a_810_, v___x_812_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; 
lean_dec_ref(v_guard_804_);
lean_dec_ref(v_O_803_);
v___x_814_ = lean_box(0);
return v___x_814_;
}
}
else
{
lean_object* v___x_815_; 
lean_dec_ref(v_guard_804_);
lean_dec_ref(v_O_803_);
v___x_815_ = lean_box(0);
return v___x_815_;
}
}
else
{
lean_object* v___x_816_; 
lean_dec_ref(v_guard_804_);
lean_dec_ref(v_O_803_);
v___x_816_ = lean_box(0);
return v___x_816_;
}
}
else
{
lean_object* v___x_817_; 
lean_dec_ref(v_guard_804_);
lean_dec_ref(v_O_803_);
v___x_817_ = lean_box(0);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__not__bool___boxed(lean_object* v_O_818_, lean_object* v_guard_819_, lean_object* v_if___820_, lean_object* v_else___821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = lp_kanon__tiny__values_Tiny_b__ite_r__not__bool(v_O_818_, v_guard_819_, v_if___820_, v_else___821_);
lean_dec_ref(v_else___821_);
lean_dec_ref(v_if___820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__then(lean_object* v_O_823_, lean_object* v_guard_824_, lean_object* v_if___825_, lean_object* v_else___826_){
_start:
{
lean_object* v_kind_827_; 
v_kind_827_ = lean_ctor_get(v_if___825_, 0);
if (lean_obj_tag(v_kind_827_) == 4)
{
uint8_t v_a_828_; 
v_a_828_ = lean_ctor_get_uint8(v_kind_827_, 0);
if (v_a_828_ == 0)
{
lean_object* v_b__and_829_; lean_object* v_b__not_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_b__and_829_ = lean_ctor_get(v_O_823_, 1);
lean_inc_ref(v_b__and_829_);
v_b__not_830_ = lean_ctor_get(v_O_823_, 3);
lean_inc_ref(v_b__not_830_);
lean_dec_ref(v_O_823_);
v___x_831_ = 1;
v___x_832_ = lean_apply_1(v_b__not_830_, v_guard_824_);
v___x_833_ = lean_apply_2(v_b__and_829_, v___x_832_, v_else___826_);
v___x_834_ = lp_kanon_Kanon_whenSome___redArg(v___x_831_, v___x_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; 
lean_dec_ref(v_else___826_);
lean_dec_ref(v_guard_824_);
lean_dec_ref(v_O_823_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
}
else
{
lean_object* v___x_836_; 
lean_dec_ref(v_else___826_);
lean_dec_ref(v_guard_824_);
lean_dec_ref(v_O_823_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__then___boxed(lean_object* v_O_837_, lean_object* v_guard_838_, lean_object* v_if___839_, lean_object* v_else___840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = lp_kanon__tiny__values_Tiny_b__ite_r__false__then(v_O_837_, v_guard_838_, v_if___839_, v_else___840_);
lean_dec_ref(v_if___839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__then(lean_object* v_O_842_, lean_object* v_guard_843_, lean_object* v_if___844_, lean_object* v_else___845_){
_start:
{
lean_object* v_kind_846_; 
v_kind_846_ = lean_ctor_get(v_if___844_, 0);
if (lean_obj_tag(v_kind_846_) == 4)
{
uint8_t v_a_847_; 
v_a_847_ = lean_ctor_get_uint8(v_kind_846_, 0);
if (v_a_847_ == 1)
{
lean_object* v_b__or_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_b__or_848_ = lean_ctor_get(v_O_842_, 2);
lean_inc_ref(v_b__or_848_);
lean_dec_ref(v_O_842_);
v___x_849_ = lean_apply_2(v_b__or_848_, v_guard_843_, v_else___845_);
v___x_850_ = lp_kanon_Kanon_whenSome___redArg(v_a_847_, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v_else___845_);
lean_dec_ref(v_guard_843_);
lean_dec_ref(v_O_842_);
v___x_851_ = lean_box(0);
return v___x_851_;
}
}
else
{
lean_object* v___x_852_; 
lean_dec_ref(v_else___845_);
lean_dec_ref(v_guard_843_);
lean_dec_ref(v_O_842_);
v___x_852_ = lean_box(0);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__then___boxed(lean_object* v_O_853_, lean_object* v_guard_854_, lean_object* v_if___855_, lean_object* v_else___856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = lp_kanon__tiny__values_Tiny_b__ite_r__true__then(v_O_853_, v_guard_854_, v_if___855_, v_else___856_);
lean_dec_ref(v_if___855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__else(lean_object* v_O_858_, lean_object* v_guard_859_, lean_object* v_if___860_, lean_object* v_else___861_){
_start:
{
lean_object* v_kind_862_; 
v_kind_862_ = lean_ctor_get(v_else___861_, 0);
if (lean_obj_tag(v_kind_862_) == 4)
{
uint8_t v_a_863_; 
v_a_863_ = lean_ctor_get_uint8(v_kind_862_, 0);
if (v_a_863_ == 0)
{
lean_object* v_b__and_864_; uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_b__and_864_ = lean_ctor_get(v_O_858_, 1);
lean_inc_ref(v_b__and_864_);
lean_dec_ref(v_O_858_);
v___x_865_ = 1;
v___x_866_ = lean_apply_2(v_b__and_864_, v_guard_859_, v_if___860_);
v___x_867_ = lp_kanon_Kanon_whenSome___redArg(v___x_865_, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v___x_868_; 
lean_dec_ref(v_if___860_);
lean_dec_ref(v_guard_859_);
lean_dec_ref(v_O_858_);
v___x_868_ = lean_box(0);
return v___x_868_;
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v_if___860_);
lean_dec_ref(v_guard_859_);
lean_dec_ref(v_O_858_);
v___x_869_ = lean_box(0);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__false__else___boxed(lean_object* v_O_870_, lean_object* v_guard_871_, lean_object* v_if___872_, lean_object* v_else___873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = lp_kanon__tiny__values_Tiny_b__ite_r__false__else(v_O_870_, v_guard_871_, v_if___872_, v_else___873_);
lean_dec_ref(v_else___873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__else(lean_object* v_O_875_, lean_object* v_guard_876_, lean_object* v_if___877_, lean_object* v_else___878_){
_start:
{
lean_object* v_kind_879_; 
v_kind_879_ = lean_ctor_get(v_else___878_, 0);
if (lean_obj_tag(v_kind_879_) == 4)
{
uint8_t v_a_880_; 
v_a_880_ = lean_ctor_get_uint8(v_kind_879_, 0);
if (v_a_880_ == 1)
{
lean_object* v_b__or_881_; lean_object* v_b__not_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_b__or_881_ = lean_ctor_get(v_O_875_, 2);
lean_inc_ref(v_b__or_881_);
v_b__not_882_ = lean_ctor_get(v_O_875_, 3);
lean_inc_ref(v_b__not_882_);
lean_dec_ref(v_O_875_);
v___x_883_ = lean_apply_1(v_b__not_882_, v_guard_876_);
v___x_884_ = lean_apply_2(v_b__or_881_, v___x_883_, v_if___877_);
v___x_885_ = lp_kanon_Kanon_whenSome___redArg(v_a_880_, v___x_884_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
lean_dec_ref(v_if___877_);
lean_dec_ref(v_guard_876_);
lean_dec_ref(v_O_875_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec_ref(v_if___877_);
lean_dec_ref(v_guard_876_);
lean_dec_ref(v_O_875_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__true__else___boxed(lean_object* v_O_888_, lean_object* v_guard_889_, lean_object* v_if___890_, lean_object* v_else___891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = lp_kanon__tiny__values_Tiny_b__ite_r__true__else(v_O_888_, v_guard_889_, v_if___890_, v_else___891_);
lean_dec_ref(v_else___891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__not__guard(lean_object* v_O_893_, lean_object* v_guard_894_, lean_object* v_if___895_, lean_object* v_else___896_){
_start:
{
lean_object* v_kind_897_; 
v_kind_897_ = lean_ctor_get(v_guard_894_, 0);
lean_inc_ref(v_kind_897_);
lean_dec_ref(v_guard_894_);
if (lean_obj_tag(v_kind_897_) == 1)
{
lean_object* v_a_898_; lean_object* v_b__ite_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_898_ = lean_ctor_get(v_kind_897_, 1);
lean_inc_ref(v_a_898_);
lean_dec_ref_known(v_kind_897_, 2);
v_b__ite_899_ = lean_ctor_get(v_O_893_, 4);
lean_inc_ref(v_b__ite_899_);
lean_dec_ref(v_O_893_);
v___x_900_ = 1;
v___x_901_ = lean_apply_3(v_b__ite_899_, v_a_898_, v_else___896_, v_if___895_);
v___x_902_ = lp_kanon_Kanon_whenSome___redArg(v___x_900_, v___x_901_);
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v_kind_897_);
lean_dec_ref(v_else___896_);
lean_dec_ref(v_if___895_);
lean_dec_ref(v_O_893_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__default___redArg(lean_object* v_guard_904_, lean_object* v_if___905_, lean_object* v_else___906_){
_start:
{
uint8_t v_ty_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_ty_907_ = lean_ctor_get_uint8(v_if___905_, sizeof(void*)*1);
v___x_908_ = 1;
v___x_909_ = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(v___x_909_, 0, v_guard_904_);
lean_ctor_set(v___x_909_, 1, v_if___905_);
lean_ctor_set(v___x_909_, 2, v_else___906_);
v___x_910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*1, v_ty_907_);
v___x_911_ = lp_kanon_Kanon_whenSome___redArg(v___x_908_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__default(lean_object* v_O_912_, lean_object* v_guard_913_, lean_object* v_if___914_, lean_object* v_else___915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lp_kanon__tiny__values_Tiny_b__ite_r__default___redArg(v_guard_913_, v_if___914_, v_else___915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__ite_r__default___boxed(lean_object* v_O_917_, lean_object* v_guard_918_, lean_object* v_if___919_, lean_object* v_else___920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = lp_kanon__tiny__values_Tiny_b__ite_r__default(v_O_917_, v_guard_918_, v_if___919_, v_else___920_);
lean_dec_ref(v_O_917_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools___redArg(lean_object* v_v1_922_, lean_object* v_v2_923_){
_start:
{
lean_object* v_kind_924_; 
v_kind_924_ = lean_ctor_get(v_v1_922_, 0);
if (lean_obj_tag(v_kind_924_) == 4)
{
lean_object* v_kind_925_; 
v_kind_925_ = lean_ctor_get(v_v2_923_, 0);
if (lean_obj_tag(v_kind_925_) == 4)
{
uint8_t v_a_926_; uint8_t v_a_927_; uint8_t v___x_928_; uint8_t v___y_930_; 
v_a_926_ = lean_ctor_get_uint8(v_kind_924_, 0);
v_a_927_ = lean_ctor_get_uint8(v_kind_925_, 0);
v___x_928_ = 1;
if (v_a_926_ == 0)
{
if (v_a_927_ == 0)
{
v___y_930_ = v___x_928_;
goto v___jp_929_;
}
else
{
v___y_930_ = v_a_926_;
goto v___jp_929_;
}
}
else
{
v___y_930_ = v_a_927_;
goto v___jp_929_;
}
v___jp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lp_kanon__tiny__values_Tiny_of__bool(v___y_930_);
v___x_932_ = lp_kanon_Kanon_whenSome___redArg(v___x_928_, v___x_931_);
return v___x_932_;
}
}
else
{
lean_object* v___x_933_; 
v___x_933_ = lean_box(0);
return v___x_933_;
}
}
else
{
lean_object* v___x_934_; 
v___x_934_ = lean_box(0);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools___redArg___boxed(lean_object* v_v1_935_, lean_object* v_v2_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = lp_kanon__tiny__values_Tiny_sem__eq_r__bools___redArg(v_v1_935_, v_v2_936_);
lean_dec_ref(v_v2_936_);
lean_dec_ref(v_v1_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools(lean_object* v_O_938_, lean_object* v_v1_939_, lean_object* v_v2_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lp_kanon__tiny__values_Tiny_sem__eq_r__bools___redArg(v_v1_939_, v_v2_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__bools___boxed(lean_object* v_O_942_, lean_object* v_v1_943_, lean_object* v_v2_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = lp_kanon__tiny__values_Tiny_sem__eq_r__bools(v_O_942_, v_v1_943_, v_v2_944_);
lean_dec_ref(v_v2_944_);
lean_dec_ref(v_v1_943_);
lean_dec_ref(v_O_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__false__(lean_object* v_O_946_, lean_object* v_v1_947_, lean_object* v_v2_948_){
_start:
{
lean_object* v___y_950_; lean_object* v_kind_957_; 
v_kind_957_ = lean_ctor_get(v_v1_947_, 0);
if (lean_obj_tag(v_kind_957_) == 4)
{
uint8_t v_a_958_; 
v_a_958_ = lean_ctor_get_uint8(v_kind_957_, 0);
if (v_a_958_ == 0)
{
lean_object* v_b__not_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_b__not_959_ = lean_ctor_get(v_O_946_, 3);
v___x_960_ = 1;
lean_inc_ref(v_b__not_959_);
lean_inc_ref(v_v2_948_);
v___x_961_ = lean_apply_1(v_b__not_959_, v_v2_948_);
v___x_962_ = lp_kanon_Kanon_whenSome___redArg(v___x_960_, v___x_961_);
if (lean_obj_tag(v___x_962_) == 0)
{
v___y_950_ = v___x_962_;
goto v___jp_949_;
}
else
{
lean_dec_ref(v_v2_948_);
lean_dec_ref(v_v1_947_);
lean_dec_ref(v_O_946_);
return v___x_962_;
}
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_box(0);
v___y_950_ = v___x_963_;
goto v___jp_949_;
}
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_box(0);
v___y_950_ = v___x_964_;
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v_kind_951_; 
v_kind_951_ = lean_ctor_get(v_v2_948_, 0);
lean_inc_ref(v_kind_951_);
lean_dec_ref(v_v2_948_);
if (lean_obj_tag(v_kind_951_) == 4)
{
uint8_t v_a_952_; 
v_a_952_ = lean_ctor_get_uint8(v_kind_951_, 0);
lean_dec_ref_known(v_kind_951_, 0);
if (v_a_952_ == 0)
{
lean_object* v_b__not_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v___y_950_);
v_b__not_953_ = lean_ctor_get(v_O_946_, 3);
lean_inc_ref(v_b__not_953_);
lean_dec_ref(v_O_946_);
v___x_954_ = 1;
v___x_955_ = lean_apply_1(v_b__not_953_, v_v1_947_);
v___x_956_ = lp_kanon_Kanon_whenSome___redArg(v___x_954_, v___x_955_);
return v___x_956_;
}
else
{
lean_dec_ref(v_v1_947_);
lean_dec_ref(v_O_946_);
return v___y_950_;
}
}
else
{
lean_dec_ref(v_kind_951_);
lean_dec_ref(v_v1_947_);
lean_dec_ref(v_O_946_);
return v___y_950_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__true___00__redArg(lean_object* v_v1_965_, lean_object* v_v2_966_){
_start:
{
lean_object* v___y_968_; lean_object* v_kind_972_; 
v_kind_972_ = lean_ctor_get(v_v1_965_, 0);
if (lean_obj_tag(v_kind_972_) == 4)
{
uint8_t v_a_973_; 
v_a_973_ = lean_ctor_get_uint8(v_kind_972_, 0);
if (v_a_973_ == 1)
{
lean_object* v___x_974_; 
lean_inc_ref(v_v2_966_);
v___x_974_ = lp_kanon_Kanon_whenSome___redArg(v_a_973_, v_v2_966_);
if (lean_obj_tag(v___x_974_) == 0)
{
v___y_968_ = v___x_974_;
goto v___jp_967_;
}
else
{
lean_dec_ref(v_v2_966_);
lean_dec_ref(v_v1_965_);
return v___x_974_;
}
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_box(0);
v___y_968_ = v___x_975_;
goto v___jp_967_;
}
}
else
{
lean_object* v___x_976_; 
v___x_976_ = lean_box(0);
v___y_968_ = v___x_976_;
goto v___jp_967_;
}
v___jp_967_:
{
lean_object* v_kind_969_; 
v_kind_969_ = lean_ctor_get(v_v2_966_, 0);
lean_inc_ref(v_kind_969_);
lean_dec_ref(v_v2_966_);
if (lean_obj_tag(v_kind_969_) == 4)
{
uint8_t v_a_970_; 
v_a_970_ = lean_ctor_get_uint8(v_kind_969_, 0);
lean_dec_ref_known(v_kind_969_, 0);
if (v_a_970_ == 1)
{
lean_object* v___x_971_; 
lean_dec(v___y_968_);
v___x_971_ = lp_kanon_Kanon_whenSome___redArg(v_a_970_, v_v1_965_);
return v___x_971_;
}
else
{
lean_dec_ref(v_v1_965_);
return v___y_968_;
}
}
else
{
lean_dec_ref(v_kind_969_);
lean_dec_ref(v_v1_965_);
return v___y_968_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__true__(lean_object* v_O_977_, lean_object* v_v1_978_, lean_object* v_v2_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = lp_kanon__tiny__values_Tiny_sem__eq_r__true___00__redArg(v_v1_978_, v_v2_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__true___00__boxed(lean_object* v_O_981_, lean_object* v_v1_982_, lean_object* v_v2_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = lp_kanon__tiny__values_Tiny_sem__eq_r__true__(v_O_981_, v_v1_982_, v_v2_983_);
lean_dec_ref(v_O_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__nots(lean_object* v_O_985_, lean_object* v_v1_986_, lean_object* v_v2_987_){
_start:
{
lean_object* v_kind_988_; 
v_kind_988_ = lean_ctor_get(v_v1_986_, 0);
lean_inc_ref(v_kind_988_);
lean_dec_ref(v_v1_986_);
if (lean_obj_tag(v_kind_988_) == 1)
{
lean_object* v_kind_989_; 
v_kind_989_ = lean_ctor_get(v_v2_987_, 0);
lean_inc_ref(v_kind_989_);
lean_dec_ref(v_v2_987_);
if (lean_obj_tag(v_kind_989_) == 1)
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v_sem__eq_992_; uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_a_990_ = lean_ctor_get(v_kind_988_, 1);
lean_inc_ref(v_a_990_);
lean_dec_ref_known(v_kind_988_, 2);
v_a_991_ = lean_ctor_get(v_kind_989_, 1);
lean_inc_ref(v_a_991_);
lean_dec_ref_known(v_kind_989_, 2);
v_sem__eq_992_ = lean_ctor_get(v_O_985_, 5);
lean_inc_ref(v_sem__eq_992_);
lean_dec_ref(v_O_985_);
v___x_993_ = 1;
v___x_994_ = lean_apply_2(v_sem__eq_992_, v_a_990_, v_a_991_);
v___x_995_ = lp_kanon_Kanon_whenSome___redArg(v___x_993_, v___x_994_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; 
lean_dec_ref_known(v_kind_988_, 2);
lean_dec_ref(v_kind_989_);
lean_dec_ref(v_O_985_);
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
else
{
lean_object* v___x_997_; 
lean_dec_ref(v_kind_988_);
lean_dec_ref(v_v2_987_);
lean_dec_ref(v_O_985_);
v___x_997_ = lean_box(0);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints___redArg(lean_object* v_v1_998_, lean_object* v_v2_999_){
_start:
{
lean_object* v_kind_1000_; 
v_kind_1000_ = lean_ctor_get(v_v1_998_, 0);
if (lean_obj_tag(v_kind_1000_) == 6)
{
lean_object* v_kind_1001_; 
v_kind_1001_ = lean_ctor_get(v_v2_999_, 0);
if (lean_obj_tag(v_kind_1001_) == 6)
{
lean_object* v_a_1002_; lean_object* v_a_1003_; uint8_t v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1002_ = lean_ctor_get(v_kind_1000_, 0);
v_a_1003_ = lean_ctor_get(v_kind_1001_, 0);
v___x_1004_ = 1;
v___x_1005_ = lean_int_dec_eq(v_a_1002_, v_a_1003_);
v___x_1006_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_1005_);
v___x_1007_ = lp_kanon_Kanon_whenSome___redArg(v___x_1004_, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_box(0);
return v___x_1008_;
}
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_box(0);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints___redArg___boxed(lean_object* v_v1_1010_, lean_object* v_v2_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = lp_kanon__tiny__values_Tiny_sem__eq_r__ints___redArg(v_v1_1010_, v_v2_1011_);
lean_dec_ref(v_v2_1011_);
lean_dec_ref(v_v1_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints(lean_object* v_O_1013_, lean_object* v_v1_1014_, lean_object* v_v2_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lp_kanon__tiny__values_Tiny_sem__eq_r__ints___redArg(v_v1_1014_, v_v2_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__ints___boxed(lean_object* v_O_1017_, lean_object* v_v1_1018_, lean_object* v_v2_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = lp_kanon__tiny__values_Tiny_sem__eq_r__ints(v_O_1017_, v_v1_1018_, v_v2_1019_);
lean_dec_ref(v_v2_1019_);
lean_dec_ref(v_v1_1018_);
lean_dec_ref(v_O_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__add__const(lean_object* v_O_1021_, lean_object* v_v1_1022_, lean_object* v_v2_1023_){
_start:
{
lean_object* v_kind_1024_; lean_object* v___y_1026_; lean_object* v___y_1041_; lean_object* v___y_1056_; 
v_kind_1024_ = lean_ctor_get(v_v1_1022_, 0);
lean_inc_ref(v_kind_1024_);
lean_dec_ref(v_v1_1022_);
if (lean_obj_tag(v_kind_1024_) == 2)
{
uint8_t v_a_1070_; 
v_a_1070_ = lean_ctor_get_uint8(v_kind_1024_, sizeof(void*)*2);
if (v_a_1070_ == 5)
{
lean_object* v_a_1071_; lean_object* v_kind_1072_; 
v_a_1071_ = lean_ctor_get(v_kind_1024_, 1);
v_kind_1072_ = lean_ctor_get(v_a_1071_, 0);
if (lean_obj_tag(v_kind_1072_) == 6)
{
lean_object* v_kind_1073_; 
v_kind_1073_ = lean_ctor_get(v_v2_1023_, 0);
if (lean_obj_tag(v_kind_1073_) == 6)
{
lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v_a_1076_; lean_object* v_sem__eq_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_a_1074_ = lean_ctor_get(v_kind_1024_, 0);
v_a_1075_ = lean_ctor_get(v_kind_1072_, 0);
v_a_1076_ = lean_ctor_get(v_kind_1073_, 0);
v_sem__eq_1077_ = lean_ctor_get(v_O_1021_, 5);
v___x_1078_ = 1;
v___x_1079_ = lean_int_sub(v_a_1076_, v_a_1075_);
v___x_1080_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1079_);
lean_inc_ref(v_sem__eq_1077_);
lean_inc_ref(v_a_1074_);
v___x_1081_ = lean_apply_2(v_sem__eq_1077_, v_a_1074_, v___x_1080_);
v___x_1082_ = lp_kanon_Kanon_whenSome___redArg(v___x_1078_, v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
v___y_1056_ = v___x_1082_;
goto v___jp_1055_;
}
else
{
lean_dec_ref_known(v_kind_1024_, 2);
lean_dec_ref(v_v2_1023_);
lean_dec_ref(v_O_1021_);
return v___x_1082_;
}
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_box(0);
v___y_1056_ = v___x_1083_;
goto v___jp_1055_;
}
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_box(0);
v___y_1056_ = v___x_1084_;
goto v___jp_1055_;
}
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_box(0);
v___y_1056_ = v___x_1085_;
goto v___jp_1055_;
}
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_box(0);
v___y_1056_ = v___x_1086_;
goto v___jp_1055_;
}
v___jp_1025_:
{
if (lean_obj_tag(v_kind_1024_) == 6)
{
lean_object* v_kind_1027_; 
v_kind_1027_ = lean_ctor_get(v_v2_1023_, 0);
lean_inc_ref(v_kind_1027_);
lean_dec_ref(v_v2_1023_);
if (lean_obj_tag(v_kind_1027_) == 2)
{
uint8_t v_a_1028_; 
v_a_1028_ = lean_ctor_get_uint8(v_kind_1027_, sizeof(void*)*2);
if (v_a_1028_ == 5)
{
lean_object* v_a_1029_; lean_object* v_kind_1030_; 
v_a_1029_ = lean_ctor_get(v_kind_1027_, 0);
v_kind_1030_ = lean_ctor_get(v_a_1029_, 0);
lean_inc_ref(v_kind_1030_);
if (lean_obj_tag(v_kind_1030_) == 6)
{
lean_object* v_a_1031_; lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v_sem__eq_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v___y_1026_);
v_a_1031_ = lean_ctor_get(v_kind_1024_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v_kind_1024_, 1);
v_a_1032_ = lean_ctor_get(v_kind_1027_, 1);
lean_inc_ref(v_a_1032_);
lean_dec_ref_known(v_kind_1027_, 2);
v_a_1033_ = lean_ctor_get(v_kind_1030_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v_kind_1030_, 1);
v_sem__eq_1034_ = lean_ctor_get(v_O_1021_, 5);
lean_inc_ref(v_sem__eq_1034_);
lean_dec_ref(v_O_1021_);
v___x_1035_ = 1;
v___x_1036_ = lean_int_sub(v_a_1031_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec(v_a_1031_);
v___x_1037_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1036_);
v___x_1038_ = lean_apply_2(v_sem__eq_1034_, v_a_1032_, v___x_1037_);
v___x_1039_ = lp_kanon_Kanon_whenSome___redArg(v___x_1035_, v___x_1038_);
return v___x_1039_;
}
else
{
lean_dec_ref(v_kind_1030_);
lean_dec_ref_known(v_kind_1027_, 2);
lean_dec_ref_known(v_kind_1024_, 1);
lean_dec_ref(v_O_1021_);
return v___y_1026_;
}
}
else
{
lean_dec_ref_known(v_kind_1027_, 2);
lean_dec_ref_known(v_kind_1024_, 1);
lean_dec_ref(v_O_1021_);
return v___y_1026_;
}
}
else
{
lean_dec_ref(v_kind_1027_);
lean_dec_ref_known(v_kind_1024_, 1);
lean_dec_ref(v_O_1021_);
return v___y_1026_;
}
}
else
{
lean_dec_ref(v_kind_1024_);
lean_dec_ref(v_v2_1023_);
lean_dec_ref(v_O_1021_);
return v___y_1026_;
}
}
v___jp_1040_:
{
if (lean_obj_tag(v_kind_1024_) == 6)
{
lean_object* v_kind_1042_; 
v_kind_1042_ = lean_ctor_get(v_v2_1023_, 0);
if (lean_obj_tag(v_kind_1042_) == 2)
{
uint8_t v_a_1043_; 
v_a_1043_ = lean_ctor_get_uint8(v_kind_1042_, sizeof(void*)*2);
if (v_a_1043_ == 5)
{
lean_object* v_a_1044_; lean_object* v_kind_1045_; 
v_a_1044_ = lean_ctor_get(v_kind_1042_, 1);
v_kind_1045_ = lean_ctor_get(v_a_1044_, 0);
if (lean_obj_tag(v_kind_1045_) == 6)
{
lean_object* v_a_1046_; lean_object* v_a_1047_; lean_object* v_a_1048_; lean_object* v_sem__eq_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v___y_1041_);
v_a_1046_ = lean_ctor_get(v_kind_1024_, 0);
v_a_1047_ = lean_ctor_get(v_kind_1042_, 0);
v_a_1048_ = lean_ctor_get(v_kind_1045_, 0);
v_sem__eq_1049_ = lean_ctor_get(v_O_1021_, 5);
v___x_1050_ = 1;
v___x_1051_ = lean_int_sub(v_a_1046_, v_a_1048_);
v___x_1052_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1051_);
lean_inc_ref(v_sem__eq_1049_);
lean_inc_ref(v_a_1047_);
v___x_1053_ = lean_apply_2(v_sem__eq_1049_, v_a_1047_, v___x_1052_);
v___x_1054_ = lp_kanon_Kanon_whenSome___redArg(v___x_1050_, v___x_1053_);
if (lean_obj_tag(v___x_1054_) == 0)
{
v___y_1026_ = v___x_1054_;
goto v___jp_1025_;
}
else
{
lean_dec_ref_known(v_kind_1024_, 1);
lean_dec_ref(v_v2_1023_);
lean_dec_ref(v_O_1021_);
return v___x_1054_;
}
}
else
{
v___y_1026_ = v___y_1041_;
goto v___jp_1025_;
}
}
else
{
v___y_1026_ = v___y_1041_;
goto v___jp_1025_;
}
}
else
{
v___y_1026_ = v___y_1041_;
goto v___jp_1025_;
}
}
else
{
v___y_1026_ = v___y_1041_;
goto v___jp_1025_;
}
}
v___jp_1055_:
{
if (lean_obj_tag(v_kind_1024_) == 2)
{
uint8_t v_a_1057_; 
v_a_1057_ = lean_ctor_get_uint8(v_kind_1024_, sizeof(void*)*2);
if (v_a_1057_ == 5)
{
lean_object* v_a_1058_; lean_object* v_kind_1059_; 
v_a_1058_ = lean_ctor_get(v_kind_1024_, 0);
v_kind_1059_ = lean_ctor_get(v_a_1058_, 0);
if (lean_obj_tag(v_kind_1059_) == 6)
{
lean_object* v_kind_1060_; 
v_kind_1060_ = lean_ctor_get(v_v2_1023_, 0);
if (lean_obj_tag(v_kind_1060_) == 6)
{
lean_object* v_a_1061_; lean_object* v_a_1062_; lean_object* v_a_1063_; lean_object* v_sem__eq_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec(v___y_1056_);
v_a_1061_ = lean_ctor_get(v_kind_1024_, 1);
v_a_1062_ = lean_ctor_get(v_kind_1059_, 0);
v_a_1063_ = lean_ctor_get(v_kind_1060_, 0);
v_sem__eq_1064_ = lean_ctor_get(v_O_1021_, 5);
v___x_1065_ = 1;
v___x_1066_ = lean_int_sub(v_a_1063_, v_a_1062_);
v___x_1067_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1066_);
lean_inc_ref(v_sem__eq_1064_);
lean_inc_ref(v_a_1061_);
v___x_1068_ = lean_apply_2(v_sem__eq_1064_, v_a_1061_, v___x_1067_);
v___x_1069_ = lp_kanon_Kanon_whenSome___redArg(v___x_1065_, v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
v___y_1041_ = v___x_1069_;
goto v___jp_1040_;
}
else
{
lean_dec_ref_known(v_kind_1024_, 2);
lean_dec_ref(v_v2_1023_);
lean_dec_ref(v_O_1021_);
return v___x_1069_;
}
}
else
{
v___y_1041_ = v___y_1056_;
goto v___jp_1040_;
}
}
else
{
v___y_1041_ = v___y_1056_;
goto v___jp_1040_;
}
}
else
{
v___y_1041_ = v___y_1056_;
goto v___jp_1040_;
}
}
else
{
v___y_1041_ = v___y_1056_;
goto v___jp_1040_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__sub__const(lean_object* v_O_1087_, lean_object* v_v1_1088_, lean_object* v_v2_1089_){
_start:
{
lean_object* v_kind_1090_; lean_object* v___y_1092_; 
v_kind_1090_ = lean_ctor_get(v_v1_1088_, 0);
lean_inc_ref(v_kind_1090_);
lean_dec_ref(v_v1_1088_);
if (lean_obj_tag(v_kind_1090_) == 2)
{
uint8_t v_a_1106_; 
v_a_1106_ = lean_ctor_get_uint8(v_kind_1090_, sizeof(void*)*2);
if (v_a_1106_ == 6)
{
lean_object* v_a_1107_; lean_object* v_kind_1108_; 
v_a_1107_ = lean_ctor_get(v_kind_1090_, 1);
v_kind_1108_ = lean_ctor_get(v_a_1107_, 0);
if (lean_obj_tag(v_kind_1108_) == 6)
{
lean_object* v_kind_1109_; 
v_kind_1109_ = lean_ctor_get(v_v2_1089_, 0);
if (lean_obj_tag(v_kind_1109_) == 6)
{
lean_object* v_a_1110_; lean_object* v_a_1111_; lean_object* v_a_1112_; lean_object* v_sem__eq_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_a_1110_ = lean_ctor_get(v_kind_1090_, 0);
v_a_1111_ = lean_ctor_get(v_kind_1108_, 0);
v_a_1112_ = lean_ctor_get(v_kind_1109_, 0);
v_sem__eq_1113_ = lean_ctor_get(v_O_1087_, 5);
v___x_1114_ = 1;
v___x_1115_ = lean_int_add(v_a_1112_, v_a_1111_);
v___x_1116_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1115_);
lean_inc_ref(v_sem__eq_1113_);
lean_inc_ref(v_a_1110_);
v___x_1117_ = lean_apply_2(v_sem__eq_1113_, v_a_1110_, v___x_1116_);
v___x_1118_ = lp_kanon_Kanon_whenSome___redArg(v___x_1114_, v___x_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
v___y_1092_ = v___x_1118_;
goto v___jp_1091_;
}
else
{
lean_dec_ref_known(v_kind_1090_, 2);
lean_dec_ref(v_v2_1089_);
lean_dec_ref(v_O_1087_);
return v___x_1118_;
}
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_box(0);
v___y_1092_ = v___x_1119_;
goto v___jp_1091_;
}
}
else
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_box(0);
v___y_1092_ = v___x_1120_;
goto v___jp_1091_;
}
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_box(0);
v___y_1092_ = v___x_1121_;
goto v___jp_1091_;
}
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_box(0);
v___y_1092_ = v___x_1122_;
goto v___jp_1091_;
}
v___jp_1091_:
{
if (lean_obj_tag(v_kind_1090_) == 6)
{
lean_object* v_kind_1093_; 
v_kind_1093_ = lean_ctor_get(v_v2_1089_, 0);
lean_inc_ref(v_kind_1093_);
lean_dec_ref(v_v2_1089_);
if (lean_obj_tag(v_kind_1093_) == 2)
{
uint8_t v_a_1094_; 
v_a_1094_ = lean_ctor_get_uint8(v_kind_1093_, sizeof(void*)*2);
if (v_a_1094_ == 6)
{
lean_object* v_a_1095_; lean_object* v_kind_1096_; 
v_a_1095_ = lean_ctor_get(v_kind_1093_, 1);
v_kind_1096_ = lean_ctor_get(v_a_1095_, 0);
lean_inc_ref(v_kind_1096_);
if (lean_obj_tag(v_kind_1096_) == 6)
{
lean_object* v_a_1097_; lean_object* v_a_1098_; lean_object* v_a_1099_; lean_object* v_sem__eq_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec(v___y_1092_);
v_a_1097_ = lean_ctor_get(v_kind_1090_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v_kind_1090_, 1);
v_a_1098_ = lean_ctor_get(v_kind_1093_, 0);
lean_inc_ref(v_a_1098_);
lean_dec_ref_known(v_kind_1093_, 2);
v_a_1099_ = lean_ctor_get(v_kind_1096_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v_kind_1096_, 1);
v_sem__eq_1100_ = lean_ctor_get(v_O_1087_, 5);
lean_inc_ref(v_sem__eq_1100_);
lean_dec_ref(v_O_1087_);
v___x_1101_ = 1;
v___x_1102_ = lean_int_add(v_a_1097_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec(v_a_1097_);
v___x_1103_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1102_);
v___x_1104_ = lean_apply_2(v_sem__eq_1100_, v_a_1098_, v___x_1103_);
v___x_1105_ = lp_kanon_Kanon_whenSome___redArg(v___x_1101_, v___x_1104_);
return v___x_1105_;
}
else
{
lean_dec_ref(v_kind_1096_);
lean_dec_ref_known(v_kind_1093_, 2);
lean_dec_ref_known(v_kind_1090_, 1);
lean_dec_ref(v_O_1087_);
return v___y_1092_;
}
}
else
{
lean_dec_ref_known(v_kind_1093_, 2);
lean_dec_ref_known(v_kind_1090_, 1);
lean_dec_ref(v_O_1087_);
return v___y_1092_;
}
}
else
{
lean_dec_ref_known(v_kind_1090_, 1);
lean_dec_ref(v_kind_1093_);
lean_dec_ref(v_O_1087_);
return v___y_1092_;
}
}
else
{
lean_dec_ref(v_kind_1090_);
lean_dec_ref(v_v2_1089_);
lean_dec_ref(v_O_1087_);
return v___y_1092_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__mul__const(lean_object* v_O_1123_, lean_object* v_v1_1124_, lean_object* v_v2_1125_){
_start:
{
lean_object* v_kind_1126_; lean_object* v___y_1128_; lean_object* v___y_1151_; lean_object* v___y_1153_; lean_object* v___y_1176_; lean_object* v___y_1178_; lean_object* v___y_1201_; 
v_kind_1126_ = lean_ctor_get(v_v1_1124_, 0);
lean_inc_ref(v_kind_1126_);
lean_dec_ref(v_v1_1124_);
if (lean_obj_tag(v_kind_1126_) == 6)
{
lean_object* v_kind_1202_; 
v_kind_1202_ = lean_ctor_get(v_v2_1125_, 0);
if (lean_obj_tag(v_kind_1202_) == 2)
{
uint8_t v_a_1203_; 
v_a_1203_ = lean_ctor_get_uint8(v_kind_1202_, sizeof(void*)*2);
if (v_a_1203_ == 7)
{
lean_object* v_a_1204_; lean_object* v_kind_1205_; 
v_a_1204_ = lean_ctor_get(v_kind_1202_, 0);
v_kind_1205_ = lean_ctor_get(v_a_1204_, 0);
if (lean_obj_tag(v_kind_1205_) == 6)
{
lean_object* v_a_1206_; lean_object* v_a_1207_; lean_object* v_a_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_a_1206_ = lean_ctor_get(v_kind_1126_, 0);
v_a_1207_ = lean_ctor_get(v_kind_1202_, 1);
v_a_1208_ = lean_ctor_get(v_kind_1205_, 0);
v___x_1209_ = 1;
v___x_1210_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1211_ = lean_int_dec_eq(v_a_1208_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_int_mod(v_a_1206_, v_a_1208_);
v___x_1213_ = lean_int_dec_eq(v___x_1212_, v___x_1210_);
lean_dec(v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0);
v___y_1201_ = v___x_1214_;
goto v___jp_1200_;
}
else
{
lean_object* v_sem__eq_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_sem__eq_1215_ = lean_ctor_get(v_O_1123_, 5);
v___x_1216_ = lean_int_div(v_a_1206_, v_a_1208_);
v___x_1217_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1216_);
lean_inc_ref(v_sem__eq_1215_);
lean_inc_ref(v_a_1207_);
v___x_1218_ = lean_apply_2(v_sem__eq_1215_, v_a_1207_, v___x_1217_);
v___x_1219_ = lp_kanon_Kanon_whenSome___redArg(v___x_1209_, v___x_1218_);
v___y_1201_ = v___x_1219_;
goto v___jp_1200_;
}
}
else
{
uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_int_dec_eq(v_a_1206_, v___x_1210_);
v___x_1221_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_1220_);
v___x_1222_ = lp_kanon_Kanon_whenSome___redArg(v___x_1209_, v___x_1221_);
v___y_1201_ = v___x_1222_;
goto v___jp_1200_;
}
}
else
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_box(0);
v___y_1178_ = v___x_1223_;
goto v___jp_1177_;
}
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_box(0);
v___y_1178_ = v___x_1224_;
goto v___jp_1177_;
}
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_box(0);
v___y_1178_ = v___x_1225_;
goto v___jp_1177_;
}
}
else
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_box(0);
v___y_1178_ = v___x_1226_;
goto v___jp_1177_;
}
v___jp_1127_:
{
if (lean_obj_tag(v_kind_1126_) == 2)
{
uint8_t v_a_1129_; 
v_a_1129_ = lean_ctor_get_uint8(v_kind_1126_, sizeof(void*)*2);
if (v_a_1129_ == 7)
{
lean_object* v_a_1130_; lean_object* v_kind_1131_; 
v_a_1130_ = lean_ctor_get(v_kind_1126_, 1);
v_kind_1131_ = lean_ctor_get(v_a_1130_, 0);
lean_inc_ref(v_kind_1131_);
if (lean_obj_tag(v_kind_1131_) == 6)
{
lean_object* v_kind_1132_; 
v_kind_1132_ = lean_ctor_get(v_v2_1125_, 0);
lean_inc_ref(v_kind_1132_);
lean_dec_ref(v_v2_1125_);
if (lean_obj_tag(v_kind_1132_) == 6)
{
lean_object* v_a_1133_; lean_object* v_a_1134_; lean_object* v_a_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
lean_dec(v___y_1128_);
v_a_1133_ = lean_ctor_get(v_kind_1126_, 0);
lean_inc_ref(v_a_1133_);
lean_dec_ref_known(v_kind_1126_, 2);
v_a_1134_ = lean_ctor_get(v_kind_1131_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v_kind_1131_, 1);
v_a_1135_ = lean_ctor_get(v_kind_1132_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v_kind_1132_, 1);
v___x_1136_ = 1;
v___x_1137_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1138_ = lean_int_dec_eq(v_a_1134_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_int_mod(v_a_1135_, v_a_1134_);
v___x_1140_ = lean_int_dec_eq(v___x_1139_, v___x_1137_);
lean_dec(v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_O_1123_);
v___x_1141_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0);
return v___x_1141_;
}
else
{
lean_object* v_sem__eq_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_sem__eq_1142_ = lean_ctor_get(v_O_1123_, 5);
lean_inc_ref(v_sem__eq_1142_);
lean_dec_ref(v_O_1123_);
v___x_1143_ = lean_int_div(v_a_1135_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec(v_a_1135_);
v___x_1144_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1143_);
v___x_1145_ = lean_apply_2(v_sem__eq_1142_, v_a_1133_, v___x_1144_);
v___x_1146_ = lp_kanon_Kanon_whenSome___redArg(v___x_1136_, v___x_1145_);
return v___x_1146_;
}
}
else
{
uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec_ref(v_O_1123_);
v___x_1147_ = lean_int_dec_eq(v_a_1135_, v___x_1137_);
lean_dec(v_a_1135_);
v___x_1148_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_1147_);
v___x_1149_ = lp_kanon_Kanon_whenSome___redArg(v___x_1136_, v___x_1148_);
return v___x_1149_;
}
}
else
{
lean_dec_ref_known(v_kind_1131_, 1);
lean_dec_ref(v_kind_1132_);
lean_dec_ref_known(v_kind_1126_, 2);
lean_dec_ref(v_O_1123_);
return v___y_1128_;
}
}
else
{
lean_dec_ref(v_kind_1131_);
lean_dec_ref_known(v_kind_1126_, 2);
lean_dec_ref(v_v2_1125_);
lean_dec_ref(v_O_1123_);
return v___y_1128_;
}
}
else
{
lean_dec_ref_known(v_kind_1126_, 2);
lean_dec_ref(v_v2_1125_);
lean_dec_ref(v_O_1123_);
return v___y_1128_;
}
}
else
{
lean_dec_ref(v_kind_1126_);
lean_dec_ref(v_v2_1125_);
lean_dec_ref(v_O_1123_);
return v___y_1128_;
}
}
v___jp_1150_:
{
if (lean_obj_tag(v___y_1151_) == 0)
{
v___y_1128_ = v___y_1151_;
goto v___jp_1127_;
}
else
{
lean_dec_ref(v_kind_1126_);
lean_dec_ref(v_v2_1125_);
lean_dec_ref(v_O_1123_);
return v___y_1151_;
}
}
v___jp_1152_:
{
if (lean_obj_tag(v_kind_1126_) == 2)
{
uint8_t v_a_1154_; 
v_a_1154_ = lean_ctor_get_uint8(v_kind_1126_, sizeof(void*)*2);
if (v_a_1154_ == 7)
{
lean_object* v_a_1155_; lean_object* v_kind_1156_; 
v_a_1155_ = lean_ctor_get(v_kind_1126_, 0);
v_kind_1156_ = lean_ctor_get(v_a_1155_, 0);
if (lean_obj_tag(v_kind_1156_) == 6)
{
lean_object* v_kind_1157_; 
v_kind_1157_ = lean_ctor_get(v_v2_1125_, 0);
if (lean_obj_tag(v_kind_1157_) == 6)
{
lean_object* v_a_1158_; lean_object* v_a_1159_; lean_object* v_a_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
lean_dec(v___y_1153_);
v_a_1158_ = lean_ctor_get(v_kind_1126_, 1);
v_a_1159_ = lean_ctor_get(v_kind_1156_, 0);
v_a_1160_ = lean_ctor_get(v_kind_1157_, 0);
v___x_1161_ = 1;
v___x_1162_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1163_ = lean_int_dec_eq(v_a_1159_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_int_mod(v_a_1160_, v_a_1159_);
v___x_1165_ = lean_int_dec_eq(v___x_1164_, v___x_1162_);
lean_dec(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0);
v___y_1151_ = v___x_1166_;
goto v___jp_1150_;
}
else
{
lean_object* v_sem__eq_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_sem__eq_1167_ = lean_ctor_get(v_O_1123_, 5);
v___x_1168_ = lean_int_div(v_a_1160_, v_a_1159_);
v___x_1169_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1168_);
lean_inc_ref(v_sem__eq_1167_);
lean_inc_ref(v_a_1158_);
v___x_1170_ = lean_apply_2(v_sem__eq_1167_, v_a_1158_, v___x_1169_);
v___x_1171_ = lp_kanon_Kanon_whenSome___redArg(v___x_1161_, v___x_1170_);
v___y_1151_ = v___x_1171_;
goto v___jp_1150_;
}
}
else
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_int_dec_eq(v_a_1160_, v___x_1162_);
v___x_1173_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_1172_);
v___x_1174_ = lp_kanon_Kanon_whenSome___redArg(v___x_1161_, v___x_1173_);
v___y_1151_ = v___x_1174_;
goto v___jp_1150_;
}
}
else
{
v___y_1128_ = v___y_1153_;
goto v___jp_1127_;
}
}
else
{
v___y_1128_ = v___y_1153_;
goto v___jp_1127_;
}
}
else
{
v___y_1128_ = v___y_1153_;
goto v___jp_1127_;
}
}
else
{
v___y_1128_ = v___y_1153_;
goto v___jp_1127_;
}
}
v___jp_1175_:
{
if (lean_obj_tag(v___y_1176_) == 0)
{
v___y_1153_ = v___y_1176_;
goto v___jp_1152_;
}
else
{
lean_dec_ref(v_kind_1126_);
lean_dec_ref(v_v2_1125_);
lean_dec_ref(v_O_1123_);
return v___y_1176_;
}
}
v___jp_1177_:
{
if (lean_obj_tag(v_kind_1126_) == 6)
{
lean_object* v_kind_1179_; 
v_kind_1179_ = lean_ctor_get(v_v2_1125_, 0);
if (lean_obj_tag(v_kind_1179_) == 2)
{
uint8_t v_a_1180_; 
v_a_1180_ = lean_ctor_get_uint8(v_kind_1179_, sizeof(void*)*2);
if (v_a_1180_ == 7)
{
lean_object* v_a_1181_; lean_object* v_kind_1182_; 
v_a_1181_ = lean_ctor_get(v_kind_1179_, 1);
v_kind_1182_ = lean_ctor_get(v_a_1181_, 0);
if (lean_obj_tag(v_kind_1182_) == 6)
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v_a_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
lean_dec(v___y_1178_);
v_a_1183_ = lean_ctor_get(v_kind_1126_, 0);
v_a_1184_ = lean_ctor_get(v_kind_1179_, 0);
v_a_1185_ = lean_ctor_get(v_kind_1182_, 0);
v___x_1186_ = 1;
v___x_1187_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1188_ = lean_int_dec_eq(v_a_1185_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = lean_int_mod(v_a_1183_, v_a_1185_);
v___x_1190_ = lean_int_dec_eq(v___x_1189_, v___x_1187_);
lean_dec(v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0, &lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_b__and_r__false___00__redArg___closed__0);
v___y_1176_ = v___x_1191_;
goto v___jp_1175_;
}
else
{
lean_object* v_sem__eq_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_sem__eq_1192_ = lean_ctor_get(v_O_1123_, 5);
v___x_1193_ = lean_int_div(v_a_1183_, v_a_1185_);
v___x_1194_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1193_);
lean_inc_ref(v_sem__eq_1192_);
lean_inc_ref(v_a_1184_);
v___x_1195_ = lean_apply_2(v_sem__eq_1192_, v_a_1184_, v___x_1194_);
v___x_1196_ = lp_kanon_Kanon_whenSome___redArg(v___x_1186_, v___x_1195_);
v___y_1176_ = v___x_1196_;
goto v___jp_1175_;
}
}
else
{
uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_int_dec_eq(v_a_1183_, v___x_1187_);
v___x_1198_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_1197_);
v___x_1199_ = lp_kanon_Kanon_whenSome___redArg(v___x_1186_, v___x_1198_);
v___y_1176_ = v___x_1199_;
goto v___jp_1175_;
}
}
else
{
v___y_1153_ = v___y_1178_;
goto v___jp_1152_;
}
}
else
{
v___y_1153_ = v___y_1178_;
goto v___jp_1152_;
}
}
else
{
v___y_1153_ = v___y_1178_;
goto v___jp_1152_;
}
}
else
{
v___y_1153_ = v___y_1178_;
goto v___jp_1152_;
}
}
v___jp_1200_:
{
if (lean_obj_tag(v___y_1201_) == 0)
{
v___y_1178_ = v___y_1201_;
goto v___jp_1177_;
}
else
{
lean_dec_ref(v_kind_1126_);
lean_dec_ref(v_v2_1125_);
lean_dec_ref(v_O_1123_);
return v___y_1201_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq_r__default(lean_object* v_O_1227_, lean_object* v_v1_1228_, lean_object* v_v2_1229_){
_start:
{
uint8_t v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = 1;
v___x_1231_ = 2;
v___x_1232_ = lp_kanon__tiny__values_Tiny_mk__commut__binop(v_O_1227_, v___x_1231_, v_v1_1228_, v_v2_1229_);
v___x_1233_ = 0;
v___x_1234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*1, v___x_1233_);
v___x_1235_ = lp_kanon_Kanon_whenSome___redArg(v___x_1230_, v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg(lean_object* v_v1_1236_, lean_object* v_v2_1237_){
_start:
{
uint8_t v___y_1239_; uint8_t v_ty_1242_; uint8_t v_ty_1243_; uint8_t v___x_1244_; 
v_ty_1242_ = lean_ctor_get_uint8(v_v1_1236_, sizeof(void*)*1);
v_ty_1243_ = lean_ctor_get_uint8(v_v2_1237_, sizeof(void*)*1);
v___x_1244_ = lp_kanon__tiny__values_Tiny_instDecidableEqTy(v_ty_1242_, v_ty_1243_);
if (v___x_1244_ == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 1;
v___y_1239_ = v___x_1245_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = 0;
v___y_1239_ = v___x_1246_;
goto v___jp_1238_;
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lp_kanon__tiny__values_Tiny_v__false;
v___x_1241_ = lp_kanon_Kanon_whenSome___redArg(v___y_1239_, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg___boxed(lean_object* v_v1_1247_, lean_object* v_v2_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg(v_v1_1247_, v_v2_1248_);
lean_dec_ref(v_v2_1248_);
lean_dec_ref(v_v1_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed(lean_object* v_O_1250_, lean_object* v_v1_1251_, lean_object* v_v2_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg(v_v1_1251_, v_v2_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___boxed(lean_object* v_O_1254_, lean_object* v_v1_1255_, lean_object* v_v2_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed(v_O_1254_, v_v1_1255_, v_v2_1256_);
lean_dec_ref(v_v2_1256_);
lean_dec_ref(v_v1_1255_);
lean_dec_ref(v_O_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__typed(lean_object* v_O_1258_, lean_object* v_v1_1259_, lean_object* v_v2_1260_){
_start:
{
lean_object* v_sem__eq_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_sem__eq_1261_ = lean_ctor_get(v_O_1258_, 5);
lean_inc_ref(v_sem__eq_1261_);
lean_dec_ref(v_O_1258_);
v___x_1262_ = 1;
v___x_1263_ = lean_apply_2(v_sem__eq_1261_, v_v1_1259_, v_v2_1260_);
v___x_1264_ = lp_kanon_Kanon_whenSome___redArg(v___x_1262_, v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sem__eq__untyped_step(lean_object* v_O_1265_, lean_object* v_v1_1266_, lean_object* v_v2_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1268_ = lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__ill__typed___redArg(v_v1_1266_, v_v2_1267_);
lean_inc_ref(v_v2_1267_);
lean_inc_ref(v_v1_1266_);
v___x_1269_ = lp_kanon__tiny__values_Tiny_sem__eq__untyped_r__typed(v_O_1265_, v_v1_1266_, v_v2_1267_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1268_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lp_kanon_Kanon_firstSome___redArg(v___x_1272_);
lean_dec_ref_known(v___x_1272_, 2);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = lp_kanon__tiny__values_Tiny_sem__eq__untyped_spec(v_v1_1266_, v_v2_1267_);
return v___x_1274_;
}
else
{
lean_object* v_val_1275_; 
lean_dec_ref(v_v2_1267_);
lean_dec_ref(v_v1_1266_);
v_val_1275_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1275_);
lean_dec_ref_known(v___x_1273_, 1);
return v_val_1275_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small___redArg(lean_object* v_l_1276_){
_start:
{
uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lp_kanon__tiny__values_Tiny_at__most__one(v_l_1276_);
v___x_1278_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_1279_ = lp_kanon_Kanon_whenSome___redArg(v___x_1277_, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small___redArg___boxed(lean_object* v_l_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = lp_kanon__tiny__values_Tiny_b__distinct_r__small___redArg(v_l_1280_);
lean_dec(v_l_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small(lean_object* v_O_1282_, lean_object* v_l_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = lp_kanon__tiny__values_Tiny_b__distinct_r__small___redArg(v_l_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__small___boxed(lean_object* v_O_1285_, lean_object* v_l_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = lp_kanon__tiny__values_Tiny_b__distinct_r__small(v_O_1285_, v_l_1286_);
lean_dec(v_l_1286_);
lean_dec_ref(v_O_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_b__distinct_r__default(lean_object* v_O_1288_, lean_object* v_l_1289_){
_start:
{
lean_object* v_orc_1290_; lean_object* v_sort__by__tag_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1304_; 
v_orc_1290_ = lean_ctor_get(v_O_1288_, 0);
lean_inc_ref(v_orc_1290_);
lean_dec_ref(v_O_1288_);
v_sort__by__tag_1291_ = lean_ctor_get(v_orc_1290_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_orc_1290_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; 
v_unused_1305_ = lean_ctor_get(v_orc_1290_, 0);
lean_dec(v_unused_1305_);
v___x_1293_ = v_orc_1290_;
v_isShared_1294_ = v_isSharedCheck_1304_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_sort__by__tag_1291_);
lean_dec(v_orc_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1304_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1295_ = 1;
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_apply_1(v_sort__by__tag_1291_, v_l_1289_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 3);
lean_ctor_set(v___x_1293_, 1, v___x_1297_);
lean_ctor_set(v___x_1293_, 0, v___x_1296_);
v___x_1299_ = v___x_1293_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = 0;
v___x_1301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*1, v___x_1300_);
v___x_1302_ = lp_kanon_Kanon_whenSome___redArg(v___x_1295_, v___x_1301_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__zero___redArg(lean_object* v_v1_1306_, lean_object* v_v2_1307_){
_start:
{
lean_object* v___y_1309_; lean_object* v_kind_1315_; 
v_kind_1315_ = lean_ctor_get(v_v1_1306_, 0);
if (lean_obj_tag(v_kind_1315_) == 6)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; 
v_a_1316_ = lean_ctor_get(v_kind_1315_, 0);
v___x_1317_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1318_ = lean_int_dec_eq(v_a_1316_, v___x_1317_);
lean_inc_ref(v_v2_1307_);
v___x_1319_ = lp_kanon_Kanon_whenSome___redArg(v___x_1318_, v_v2_1307_);
if (lean_obj_tag(v___x_1319_) == 0)
{
v___y_1309_ = v___x_1319_;
goto v___jp_1308_;
}
else
{
lean_dec_ref(v_v2_1307_);
lean_dec_ref(v_v1_1306_);
return v___x_1319_;
}
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_box(0);
v___y_1309_ = v___x_1320_;
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v_kind_1310_; 
v_kind_1310_ = lean_ctor_get(v_v2_1307_, 0);
lean_inc_ref(v_kind_1310_);
lean_dec_ref(v_v2_1307_);
if (lean_obj_tag(v_kind_1310_) == 6)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; 
lean_dec(v___y_1309_);
v_a_1311_ = lean_ctor_get(v_kind_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v_kind_1310_, 1);
v___x_1312_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1313_ = lean_int_dec_eq(v_a_1311_, v___x_1312_);
lean_dec(v_a_1311_);
v___x_1314_ = lp_kanon_Kanon_whenSome___redArg(v___x_1313_, v_v1_1306_);
return v___x_1314_;
}
else
{
lean_dec_ref(v_kind_1310_);
lean_dec_ref(v_v1_1306_);
return v___y_1309_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__zero(lean_object* v_O_1321_, lean_object* v_v1_1322_, lean_object* v_v2_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = lp_kanon__tiny__values_Tiny_add_r__zero___redArg(v_v1_1322_, v_v2_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__zero___boxed(lean_object* v_O_1325_, lean_object* v_v1_1326_, lean_object* v_v2_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = lp_kanon__tiny__values_Tiny_add_r__zero(v_O_1325_, v_v1_1326_, v_v2_1327_);
lean_dec_ref(v_O_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits___redArg(lean_object* v_v1_1329_, lean_object* v_v2_1330_){
_start:
{
lean_object* v_kind_1331_; 
v_kind_1331_ = lean_ctor_get(v_v1_1329_, 0);
if (lean_obj_tag(v_kind_1331_) == 6)
{
lean_object* v_kind_1332_; 
v_kind_1332_ = lean_ctor_get(v_v2_1330_, 0);
if (lean_obj_tag(v_kind_1332_) == 6)
{
lean_object* v_a_1333_; lean_object* v_a_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_a_1333_ = lean_ctor_get(v_kind_1331_, 0);
v_a_1334_ = lean_ctor_get(v_kind_1332_, 0);
v___x_1335_ = 1;
v___x_1336_ = lean_int_add(v_a_1333_, v_a_1334_);
v___x_1337_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1336_);
v___x_1338_ = lp_kanon_Kanon_whenSome___redArg(v___x_1335_, v___x_1337_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_box(0);
return v___x_1339_;
}
}
else
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_box(0);
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits___redArg___boxed(lean_object* v_v1_1341_, lean_object* v_v2_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = lp_kanon__tiny__values_Tiny_add_r__lits___redArg(v_v1_1341_, v_v2_1342_);
lean_dec_ref(v_v2_1342_);
lean_dec_ref(v_v1_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits(lean_object* v_O_1344_, lean_object* v_v1_1345_, lean_object* v_v2_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = lp_kanon__tiny__values_Tiny_add_r__lits___redArg(v_v1_1345_, v_v2_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__lits___boxed(lean_object* v_O_1348_, lean_object* v_v1_1349_, lean_object* v_v2_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = lp_kanon__tiny__values_Tiny_add_r__lits(v_O_1348_, v_v1_1349_, v_v2_1350_);
lean_dec_ref(v_v2_1350_);
lean_dec_ref(v_v1_1349_);
lean_dec_ref(v_O_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__assoc(lean_object* v_O_1352_, lean_object* v_v1_1353_, lean_object* v_v2_1354_){
_start:
{
lean_object* v_kind_1355_; lean_object* v___y_1357_; lean_object* v___y_1372_; lean_object* v___y_1387_; 
v_kind_1355_ = lean_ctor_get(v_v1_1353_, 0);
lean_inc_ref(v_kind_1355_);
lean_dec_ref(v_v1_1353_);
if (lean_obj_tag(v_kind_1355_) == 2)
{
uint8_t v_a_1401_; 
v_a_1401_ = lean_ctor_get_uint8(v_kind_1355_, sizeof(void*)*2);
if (v_a_1401_ == 5)
{
lean_object* v_a_1402_; lean_object* v_kind_1403_; 
v_a_1402_ = lean_ctor_get(v_kind_1355_, 1);
v_kind_1403_ = lean_ctor_get(v_a_1402_, 0);
if (lean_obj_tag(v_kind_1403_) == 6)
{
lean_object* v_kind_1404_; 
v_kind_1404_ = lean_ctor_get(v_v2_1354_, 0);
if (lean_obj_tag(v_kind_1404_) == 6)
{
lean_object* v_a_1405_; lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v_add_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_a_1405_ = lean_ctor_get(v_kind_1355_, 0);
v_a_1406_ = lean_ctor_get(v_kind_1403_, 0);
v_a_1407_ = lean_ctor_get(v_kind_1404_, 0);
v_add_1408_ = lean_ctor_get(v_O_1352_, 8);
v___x_1409_ = 1;
v___x_1410_ = lean_int_add(v_a_1406_, v_a_1407_);
v___x_1411_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1410_);
lean_inc_ref(v_add_1408_);
lean_inc_ref(v_a_1405_);
v___x_1412_ = lean_apply_2(v_add_1408_, v_a_1405_, v___x_1411_);
v___x_1413_ = lp_kanon_Kanon_whenSome___redArg(v___x_1409_, v___x_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
v___y_1387_ = v___x_1413_;
goto v___jp_1386_;
}
else
{
lean_dec_ref_known(v_kind_1355_, 2);
lean_dec_ref(v_v2_1354_);
lean_dec_ref(v_O_1352_);
return v___x_1413_;
}
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_box(0);
v___y_1387_ = v___x_1414_;
goto v___jp_1386_;
}
}
else
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_box(0);
v___y_1387_ = v___x_1415_;
goto v___jp_1386_;
}
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_box(0);
v___y_1387_ = v___x_1416_;
goto v___jp_1386_;
}
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_box(0);
v___y_1387_ = v___x_1417_;
goto v___jp_1386_;
}
v___jp_1356_:
{
if (lean_obj_tag(v_kind_1355_) == 6)
{
lean_object* v_kind_1358_; 
v_kind_1358_ = lean_ctor_get(v_v2_1354_, 0);
lean_inc_ref(v_kind_1358_);
lean_dec_ref(v_v2_1354_);
if (lean_obj_tag(v_kind_1358_) == 2)
{
uint8_t v_a_1359_; 
v_a_1359_ = lean_ctor_get_uint8(v_kind_1358_, sizeof(void*)*2);
if (v_a_1359_ == 5)
{
lean_object* v_a_1360_; lean_object* v_kind_1361_; 
v_a_1360_ = lean_ctor_get(v_kind_1358_, 0);
v_kind_1361_ = lean_ctor_get(v_a_1360_, 0);
lean_inc_ref(v_kind_1361_);
if (lean_obj_tag(v_kind_1361_) == 6)
{
lean_object* v_a_1362_; lean_object* v_a_1363_; lean_object* v_a_1364_; lean_object* v_add_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v___y_1357_);
v_a_1362_ = lean_ctor_get(v_kind_1355_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v_kind_1355_, 1);
v_a_1363_ = lean_ctor_get(v_kind_1358_, 1);
lean_inc_ref(v_a_1363_);
lean_dec_ref_known(v_kind_1358_, 2);
v_a_1364_ = lean_ctor_get(v_kind_1361_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v_kind_1361_, 1);
v_add_1365_ = lean_ctor_get(v_O_1352_, 8);
lean_inc_ref(v_add_1365_);
lean_dec_ref(v_O_1352_);
v___x_1366_ = 1;
v___x_1367_ = lean_int_add(v_a_1364_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec(v_a_1364_);
v___x_1368_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1367_);
v___x_1369_ = lean_apply_2(v_add_1365_, v_a_1363_, v___x_1368_);
v___x_1370_ = lp_kanon_Kanon_whenSome___redArg(v___x_1366_, v___x_1369_);
return v___x_1370_;
}
else
{
lean_dec_ref(v_kind_1361_);
lean_dec_ref_known(v_kind_1358_, 2);
lean_dec_ref_known(v_kind_1355_, 1);
lean_dec_ref(v_O_1352_);
return v___y_1357_;
}
}
else
{
lean_dec_ref_known(v_kind_1358_, 2);
lean_dec_ref_known(v_kind_1355_, 1);
lean_dec_ref(v_O_1352_);
return v___y_1357_;
}
}
else
{
lean_dec_ref_known(v_kind_1355_, 1);
lean_dec_ref(v_kind_1358_);
lean_dec_ref(v_O_1352_);
return v___y_1357_;
}
}
else
{
lean_dec_ref(v_kind_1355_);
lean_dec_ref(v_v2_1354_);
lean_dec_ref(v_O_1352_);
return v___y_1357_;
}
}
v___jp_1371_:
{
if (lean_obj_tag(v_kind_1355_) == 6)
{
lean_object* v_kind_1373_; 
v_kind_1373_ = lean_ctor_get(v_v2_1354_, 0);
if (lean_obj_tag(v_kind_1373_) == 2)
{
uint8_t v_a_1374_; 
v_a_1374_ = lean_ctor_get_uint8(v_kind_1373_, sizeof(void*)*2);
if (v_a_1374_ == 5)
{
lean_object* v_a_1375_; lean_object* v_kind_1376_; 
v_a_1375_ = lean_ctor_get(v_kind_1373_, 1);
v_kind_1376_ = lean_ctor_get(v_a_1375_, 0);
if (lean_obj_tag(v_kind_1376_) == 6)
{
lean_object* v_a_1377_; lean_object* v_a_1378_; lean_object* v_a_1379_; lean_object* v_add_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v___y_1372_);
v_a_1377_ = lean_ctor_get(v_kind_1355_, 0);
v_a_1378_ = lean_ctor_get(v_kind_1373_, 0);
v_a_1379_ = lean_ctor_get(v_kind_1376_, 0);
v_add_1380_ = lean_ctor_get(v_O_1352_, 8);
v___x_1381_ = 1;
v___x_1382_ = lean_int_add(v_a_1379_, v_a_1377_);
v___x_1383_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1382_);
lean_inc_ref(v_add_1380_);
lean_inc_ref(v_a_1378_);
v___x_1384_ = lean_apply_2(v_add_1380_, v_a_1378_, v___x_1383_);
v___x_1385_ = lp_kanon_Kanon_whenSome___redArg(v___x_1381_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
v___y_1357_ = v___x_1385_;
goto v___jp_1356_;
}
else
{
lean_dec_ref_known(v_kind_1355_, 1);
lean_dec_ref(v_v2_1354_);
lean_dec_ref(v_O_1352_);
return v___x_1385_;
}
}
else
{
v___y_1357_ = v___y_1372_;
goto v___jp_1356_;
}
}
else
{
v___y_1357_ = v___y_1372_;
goto v___jp_1356_;
}
}
else
{
v___y_1357_ = v___y_1372_;
goto v___jp_1356_;
}
}
else
{
v___y_1357_ = v___y_1372_;
goto v___jp_1356_;
}
}
v___jp_1386_:
{
if (lean_obj_tag(v_kind_1355_) == 2)
{
uint8_t v_a_1388_; 
v_a_1388_ = lean_ctor_get_uint8(v_kind_1355_, sizeof(void*)*2);
if (v_a_1388_ == 5)
{
lean_object* v_a_1389_; lean_object* v_kind_1390_; 
v_a_1389_ = lean_ctor_get(v_kind_1355_, 0);
v_kind_1390_ = lean_ctor_get(v_a_1389_, 0);
if (lean_obj_tag(v_kind_1390_) == 6)
{
lean_object* v_kind_1391_; 
v_kind_1391_ = lean_ctor_get(v_v2_1354_, 0);
if (lean_obj_tag(v_kind_1391_) == 6)
{
lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v_a_1394_; lean_object* v_add_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v___y_1387_);
v_a_1392_ = lean_ctor_get(v_kind_1355_, 1);
v_a_1393_ = lean_ctor_get(v_kind_1390_, 0);
v_a_1394_ = lean_ctor_get(v_kind_1391_, 0);
v_add_1395_ = lean_ctor_get(v_O_1352_, 8);
v___x_1396_ = 1;
v___x_1397_ = lean_int_add(v_a_1393_, v_a_1394_);
v___x_1398_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1397_);
lean_inc_ref(v_add_1395_);
lean_inc_ref(v_a_1392_);
v___x_1399_ = lean_apply_2(v_add_1395_, v_a_1392_, v___x_1398_);
v___x_1400_ = lp_kanon_Kanon_whenSome___redArg(v___x_1396_, v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
v___y_1372_ = v___x_1400_;
goto v___jp_1371_;
}
else
{
lean_dec_ref_known(v_kind_1355_, 2);
lean_dec_ref(v_v2_1354_);
lean_dec_ref(v_O_1352_);
return v___x_1400_;
}
}
else
{
v___y_1372_ = v___y_1387_;
goto v___jp_1371_;
}
}
else
{
v___y_1372_ = v___y_1387_;
goto v___jp_1371_;
}
}
else
{
v___y_1372_ = v___y_1387_;
goto v___jp_1371_;
}
}
else
{
v___y_1372_ = v___y_1387_;
goto v___jp_1371_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_r__default(lean_object* v_O_1418_, lean_object* v_v1_1419_, lean_object* v_v2_1420_){
_start:
{
uint8_t v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1421_ = 1;
v___x_1422_ = 5;
v___x_1423_ = lp_kanon__tiny__values_Tiny_mk__commut__binop(v_O_1418_, v___x_1422_, v_v1_1419_, v_v2_1420_);
v___x_1424_ = 1;
v___x_1425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*1, v___x_1424_);
v___x_1426_ = lp_kanon_Kanon_whenSome___redArg(v___x_1421_, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_add_step(lean_object* v_O_1427_, lean_object* v_v1_1428_, lean_object* v_v2_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_inc_ref_n(v_v2_1429_, 3);
lean_inc_ref_n(v_v1_1428_, 3);
v___x_1430_ = lp_kanon__tiny__values_Tiny_add_r__zero___redArg(v_v1_1428_, v_v2_1429_);
v___x_1431_ = lp_kanon__tiny__values_Tiny_add_r__lits___redArg(v_v1_1428_, v_v2_1429_);
lean_inc_ref(v_O_1427_);
v___x_1432_ = lp_kanon__tiny__values_Tiny_add_r__assoc(v_O_1427_, v_v1_1428_, v_v2_1429_);
v___x_1433_ = lp_kanon__tiny__values_Tiny_add_r__default(v_O_1427_, v_v1_1428_, v_v2_1429_);
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1432_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1431_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1430_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lp_kanon_Kanon_firstSome___redArg(v___x_1438_);
lean_dec_ref_known(v___x_1438_, 2);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = lp_kanon__tiny__values_Tiny_add_spec(v_v1_1428_, v_v2_1429_);
return v___x_1440_;
}
else
{
lean_object* v_val_1441_; 
lean_dec_ref(v_v2_1429_);
lean_dec_ref(v_v1_1428_);
v_val_1441_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___x_1439_, 1);
return v_val_1441_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero___redArg(lean_object* v_v1_1442_, lean_object* v_v2_1443_){
_start:
{
lean_object* v_kind_1444_; 
v_kind_1444_ = lean_ctor_get(v_v2_1443_, 0);
if (lean_obj_tag(v_kind_1444_) == 6)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; 
v_a_1445_ = lean_ctor_get(v_kind_1444_, 0);
v___x_1446_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1447_ = lean_int_dec_eq(v_a_1445_, v___x_1446_);
v___x_1448_ = lp_kanon_Kanon_whenSome___redArg(v___x_1447_, v_v1_1442_);
return v___x_1448_;
}
else
{
lean_object* v___x_1449_; 
lean_dec_ref(v_v1_1442_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero___redArg___boxed(lean_object* v_v1_1450_, lean_object* v_v2_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = lp_kanon__tiny__values_Tiny_sub_r__zero___redArg(v_v1_1450_, v_v2_1451_);
lean_dec_ref(v_v2_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero(lean_object* v_O_1453_, lean_object* v_v1_1454_, lean_object* v_v2_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lp_kanon__tiny__values_Tiny_sub_r__zero___redArg(v_v1_1454_, v_v2_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__zero___boxed(lean_object* v_O_1457_, lean_object* v_v1_1458_, lean_object* v_v2_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = lp_kanon__tiny__values_Tiny_sub_r__zero(v_O_1457_, v_v1_1458_, v_v2_1459_);
lean_dec_ref(v_v2_1459_);
lean_dec_ref(v_O_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits___redArg(lean_object* v_v1_1461_, lean_object* v_v2_1462_){
_start:
{
lean_object* v_kind_1463_; 
v_kind_1463_ = lean_ctor_get(v_v1_1461_, 0);
if (lean_obj_tag(v_kind_1463_) == 6)
{
lean_object* v_kind_1464_; 
v_kind_1464_ = lean_ctor_get(v_v2_1462_, 0);
if (lean_obj_tag(v_kind_1464_) == 6)
{
lean_object* v_a_1465_; lean_object* v_a_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_a_1465_ = lean_ctor_get(v_kind_1463_, 0);
v_a_1466_ = lean_ctor_get(v_kind_1464_, 0);
v___x_1467_ = 1;
v___x_1468_ = lean_int_sub(v_a_1465_, v_a_1466_);
v___x_1469_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1468_);
v___x_1470_ = lp_kanon_Kanon_whenSome___redArg(v___x_1467_, v___x_1469_);
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits___redArg___boxed(lean_object* v_v1_1473_, lean_object* v_v2_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = lp_kanon__tiny__values_Tiny_sub_r__lits___redArg(v_v1_1473_, v_v2_1474_);
lean_dec_ref(v_v2_1474_);
lean_dec_ref(v_v1_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits(lean_object* v_O_1476_, lean_object* v_v1_1477_, lean_object* v_v2_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lp_kanon__tiny__values_Tiny_sub_r__lits___redArg(v_v1_1477_, v_v2_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__lits___boxed(lean_object* v_O_1480_, lean_object* v_v1_1481_, lean_object* v_v2_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = lp_kanon__tiny__values_Tiny_sub_r__lits(v_O_1480_, v_v1_1481_, v_v2_1482_);
lean_dec_ref(v_v2_1482_);
lean_dec_ref(v_v1_1481_);
lean_dec_ref(v_O_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars___redArg(lean_object* v_v1_1484_, lean_object* v_v2_1485_){
_start:
{
lean_object* v_kind_1486_; 
v_kind_1486_ = lean_ctor_get(v_v1_1484_, 0);
if (lean_obj_tag(v_kind_1486_) == 0)
{
lean_object* v_kind_1487_; 
v_kind_1487_ = lean_ctor_get(v_v2_1485_, 0);
if (lean_obj_tag(v_kind_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v_a_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_a_1488_ = lean_ctor_get(v_kind_1486_, 0);
v_a_1489_ = lean_ctor_get(v_kind_1487_, 0);
v___x_1490_ = lean_int_dec_eq(v_a_1488_, v_a_1489_);
v___x_1491_ = lp_kanon__tiny__values_Tiny_zero;
v___x_1492_ = lp_kanon_Kanon_whenSome___redArg(v___x_1490_, v___x_1491_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_box(0);
return v___x_1493_;
}
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars___redArg___boxed(lean_object* v_v1_1495_, lean_object* v_v2_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = lp_kanon__tiny__values_Tiny_sub_r__vars___redArg(v_v1_1495_, v_v2_1496_);
lean_dec_ref(v_v2_1496_);
lean_dec_ref(v_v1_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars(lean_object* v_O_1498_, lean_object* v_v1_1499_, lean_object* v_v2_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lp_kanon__tiny__values_Tiny_sub_r__vars___redArg(v_v1_1499_, v_v2_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__vars___boxed(lean_object* v_O_1502_, lean_object* v_v1_1503_, lean_object* v_v2_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = lp_kanon__tiny__values_Tiny_sub_r__vars(v_O_1502_, v_v1_1503_, v_v2_1504_);
lean_dec_ref(v_v2_1504_);
lean_dec_ref(v_v1_1503_);
lean_dec_ref(v_O_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__left(lean_object* v_O_1506_, lean_object* v_v1_1507_, lean_object* v_v2_1508_){
_start:
{
lean_object* v_kind_1509_; 
v_kind_1509_ = lean_ctor_get(v_v1_1507_, 0);
lean_inc_ref(v_kind_1509_);
lean_dec_ref(v_v1_1507_);
if (lean_obj_tag(v_kind_1509_) == 2)
{
uint8_t v_a_1510_; 
v_a_1510_ = lean_ctor_get_uint8(v_kind_1509_, sizeof(void*)*2);
if (v_a_1510_ == 6)
{
lean_object* v_a_1511_; lean_object* v_kind_1512_; 
v_a_1511_ = lean_ctor_get(v_kind_1509_, 0);
v_kind_1512_ = lean_ctor_get(v_a_1511_, 0);
lean_inc_ref(v_kind_1512_);
if (lean_obj_tag(v_kind_1512_) == 6)
{
lean_object* v_kind_1513_; 
v_kind_1513_ = lean_ctor_get(v_v2_1508_, 0);
if (lean_obj_tag(v_kind_1513_) == 6)
{
lean_object* v_a_1514_; lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v_sub_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1514_ = lean_ctor_get(v_kind_1509_, 1);
lean_inc_ref(v_a_1514_);
lean_dec_ref_known(v_kind_1509_, 2);
v_a_1515_ = lean_ctor_get(v_kind_1512_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v_kind_1512_, 1);
v_a_1516_ = lean_ctor_get(v_kind_1513_, 0);
v_sub_1517_ = lean_ctor_get(v_O_1506_, 9);
lean_inc_ref(v_sub_1517_);
lean_dec_ref(v_O_1506_);
v___x_1518_ = 1;
v___x_1519_ = lean_int_sub(v_a_1515_, v_a_1516_);
lean_dec(v_a_1515_);
v___x_1520_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1519_);
v___x_1521_ = lean_apply_2(v_sub_1517_, v___x_1520_, v_a_1514_);
v___x_1522_ = lp_kanon_Kanon_whenSome___redArg(v___x_1518_, v___x_1521_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref_known(v_kind_1512_, 1);
lean_dec_ref_known(v_kind_1509_, 2);
lean_dec_ref(v_O_1506_);
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
}
else
{
lean_object* v___x_1524_; 
lean_dec_ref(v_kind_1512_);
lean_dec_ref_known(v_kind_1509_, 2);
lean_dec_ref(v_O_1506_);
v___x_1524_ = lean_box(0);
return v___x_1524_;
}
}
else
{
lean_object* v___x_1525_; 
lean_dec_ref_known(v_kind_1509_, 2);
lean_dec_ref(v_O_1506_);
v___x_1525_ = lean_box(0);
return v___x_1525_;
}
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v_kind_1509_);
lean_dec_ref(v_O_1506_);
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__left___boxed(lean_object* v_O_1527_, lean_object* v_v1_1528_, lean_object* v_v2_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = lp_kanon__tiny__values_Tiny_sub_r__sub__left(v_O_1527_, v_v1_1528_, v_v2_1529_);
lean_dec_ref(v_v2_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__right(lean_object* v_O_1531_, lean_object* v_v1_1532_, lean_object* v_v2_1533_){
_start:
{
lean_object* v_kind_1534_; 
v_kind_1534_ = lean_ctor_get(v_v1_1532_, 0);
lean_inc_ref(v_kind_1534_);
lean_dec_ref(v_v1_1532_);
if (lean_obj_tag(v_kind_1534_) == 2)
{
uint8_t v_a_1535_; 
v_a_1535_ = lean_ctor_get_uint8(v_kind_1534_, sizeof(void*)*2);
if (v_a_1535_ == 6)
{
lean_object* v_a_1536_; lean_object* v_kind_1537_; 
v_a_1536_ = lean_ctor_get(v_kind_1534_, 1);
v_kind_1537_ = lean_ctor_get(v_a_1536_, 0);
lean_inc_ref(v_kind_1537_);
if (lean_obj_tag(v_kind_1537_) == 6)
{
lean_object* v_kind_1538_; 
v_kind_1538_ = lean_ctor_get(v_v2_1533_, 0);
if (lean_obj_tag(v_kind_1538_) == 6)
{
lean_object* v_a_1539_; lean_object* v_a_1540_; lean_object* v_a_1541_; lean_object* v_sub_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_a_1539_ = lean_ctor_get(v_kind_1534_, 0);
lean_inc_ref(v_a_1539_);
lean_dec_ref_known(v_kind_1534_, 2);
v_a_1540_ = lean_ctor_get(v_kind_1537_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v_kind_1537_, 1);
v_a_1541_ = lean_ctor_get(v_kind_1538_, 0);
v_sub_1542_ = lean_ctor_get(v_O_1531_, 9);
lean_inc_ref(v_sub_1542_);
lean_dec_ref(v_O_1531_);
v___x_1543_ = 1;
v___x_1544_ = lean_int_add(v_a_1540_, v_a_1541_);
lean_dec(v_a_1540_);
v___x_1545_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1544_);
v___x_1546_ = lean_apply_2(v_sub_1542_, v_a_1539_, v___x_1545_);
v___x_1547_ = lp_kanon_Kanon_whenSome___redArg(v___x_1543_, v___x_1546_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; 
lean_dec_ref_known(v_kind_1537_, 1);
lean_dec_ref_known(v_kind_1534_, 2);
lean_dec_ref(v_O_1531_);
v___x_1548_ = lean_box(0);
return v___x_1548_;
}
}
else
{
lean_object* v___x_1549_; 
lean_dec_ref(v_kind_1537_);
lean_dec_ref_known(v_kind_1534_, 2);
lean_dec_ref(v_O_1531_);
v___x_1549_ = lean_box(0);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1550_; 
lean_dec_ref_known(v_kind_1534_, 2);
lean_dec_ref(v_O_1531_);
v___x_1550_ = lean_box(0);
return v___x_1550_;
}
}
else
{
lean_object* v___x_1551_; 
lean_dec_ref(v_kind_1534_);
lean_dec_ref(v_O_1531_);
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__sub__right___boxed(lean_object* v_O_1552_, lean_object* v_v1_1553_, lean_object* v_v2_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = lp_kanon__tiny__values_Tiny_sub_r__sub__right(v_O_1552_, v_v1_1553_, v_v2_1554_);
lean_dec_ref(v_v2_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__left__sub(lean_object* v_O_1556_, lean_object* v_v1_1557_, lean_object* v_v2_1558_){
_start:
{
lean_object* v_kind_1559_; 
v_kind_1559_ = lean_ctor_get(v_v1_1557_, 0);
if (lean_obj_tag(v_kind_1559_) == 6)
{
lean_object* v_kind_1560_; 
v_kind_1560_ = lean_ctor_get(v_v2_1558_, 0);
lean_inc_ref(v_kind_1560_);
lean_dec_ref(v_v2_1558_);
if (lean_obj_tag(v_kind_1560_) == 2)
{
uint8_t v_a_1561_; 
v_a_1561_ = lean_ctor_get_uint8(v_kind_1560_, sizeof(void*)*2);
if (v_a_1561_ == 6)
{
lean_object* v_a_1562_; lean_object* v_kind_1563_; 
v_a_1562_ = lean_ctor_get(v_kind_1560_, 0);
v_kind_1563_ = lean_ctor_get(v_a_1562_, 0);
lean_inc_ref(v_kind_1563_);
if (lean_obj_tag(v_kind_1563_) == 6)
{
lean_object* v_a_1564_; lean_object* v_a_1565_; lean_object* v_a_1566_; lean_object* v_add_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1564_ = lean_ctor_get(v_kind_1559_, 0);
v_a_1565_ = lean_ctor_get(v_kind_1560_, 1);
lean_inc_ref(v_a_1565_);
lean_dec_ref_known(v_kind_1560_, 2);
v_a_1566_ = lean_ctor_get(v_kind_1563_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v_kind_1563_, 1);
v_add_1567_ = lean_ctor_get(v_O_1556_, 8);
lean_inc_ref(v_add_1567_);
lean_dec_ref(v_O_1556_);
v___x_1568_ = 1;
v___x_1569_ = lean_int_sub(v_a_1564_, v_a_1566_);
lean_dec(v_a_1566_);
v___x_1570_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1569_);
v___x_1571_ = lean_apply_2(v_add_1567_, v___x_1570_, v_a_1565_);
v___x_1572_ = lp_kanon_Kanon_whenSome___redArg(v___x_1568_, v___x_1571_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; 
lean_dec_ref(v_kind_1563_);
lean_dec_ref_known(v_kind_1560_, 2);
lean_dec_ref(v_O_1556_);
v___x_1573_ = lean_box(0);
return v___x_1573_;
}
}
else
{
lean_object* v___x_1574_; 
lean_dec_ref_known(v_kind_1560_, 2);
lean_dec_ref(v_O_1556_);
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; 
lean_dec_ref(v_kind_1560_);
lean_dec_ref(v_O_1556_);
v___x_1575_ = lean_box(0);
return v___x_1575_;
}
}
else
{
lean_object* v___x_1576_; 
lean_dec_ref(v_v2_1558_);
lean_dec_ref(v_O_1556_);
v___x_1576_ = lean_box(0);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__left__sub___boxed(lean_object* v_O_1577_, lean_object* v_v1_1578_, lean_object* v_v2_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = lp_kanon__tiny__values_Tiny_sub_r__left__sub(v_O_1577_, v_v1_1578_, v_v2_1579_);
lean_dec_ref(v_v1_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__right__sub(lean_object* v_O_1581_, lean_object* v_v1_1582_, lean_object* v_v2_1583_){
_start:
{
lean_object* v_kind_1584_; 
v_kind_1584_ = lean_ctor_get(v_v1_1582_, 0);
if (lean_obj_tag(v_kind_1584_) == 6)
{
lean_object* v_kind_1585_; 
v_kind_1585_ = lean_ctor_get(v_v2_1583_, 0);
lean_inc_ref(v_kind_1585_);
lean_dec_ref(v_v2_1583_);
if (lean_obj_tag(v_kind_1585_) == 2)
{
uint8_t v_a_1586_; 
v_a_1586_ = lean_ctor_get_uint8(v_kind_1585_, sizeof(void*)*2);
if (v_a_1586_ == 6)
{
lean_object* v_a_1587_; lean_object* v_kind_1588_; 
v_a_1587_ = lean_ctor_get(v_kind_1585_, 1);
v_kind_1588_ = lean_ctor_get(v_a_1587_, 0);
lean_inc_ref(v_kind_1588_);
if (lean_obj_tag(v_kind_1588_) == 6)
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v_sub_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1589_ = lean_ctor_get(v_kind_1584_, 0);
v_a_1590_ = lean_ctor_get(v_kind_1585_, 0);
lean_inc_ref(v_a_1590_);
lean_dec_ref_known(v_kind_1585_, 2);
v_a_1591_ = lean_ctor_get(v_kind_1588_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v_kind_1588_, 1);
v_sub_1592_ = lean_ctor_get(v_O_1581_, 9);
lean_inc_ref(v_sub_1592_);
lean_dec_ref(v_O_1581_);
v___x_1593_ = 1;
v___x_1594_ = lean_int_add(v_a_1589_, v_a_1591_);
lean_dec(v_a_1591_);
v___x_1595_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1594_);
v___x_1596_ = lean_apply_2(v_sub_1592_, v___x_1595_, v_a_1590_);
v___x_1597_ = lp_kanon_Kanon_whenSome___redArg(v___x_1593_, v___x_1596_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; 
lean_dec_ref(v_kind_1588_);
lean_dec_ref_known(v_kind_1585_, 2);
lean_dec_ref(v_O_1581_);
v___x_1598_ = lean_box(0);
return v___x_1598_;
}
}
else
{
lean_object* v___x_1599_; 
lean_dec_ref_known(v_kind_1585_, 2);
lean_dec_ref(v_O_1581_);
v___x_1599_ = lean_box(0);
return v___x_1599_;
}
}
else
{
lean_object* v___x_1600_; 
lean_dec_ref(v_kind_1585_);
lean_dec_ref(v_O_1581_);
v___x_1600_ = lean_box(0);
return v___x_1600_;
}
}
else
{
lean_object* v___x_1601_; 
lean_dec_ref(v_v2_1583_);
lean_dec_ref(v_O_1581_);
v___x_1601_ = lean_box(0);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__right__sub___boxed(lean_object* v_O_1602_, lean_object* v_v1_1603_, lean_object* v_v2_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = lp_kanon__tiny__values_Tiny_sub_r__right__sub(v_O_1602_, v_v1_1603_, v_v2_1604_);
lean_dec_ref(v_v1_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__default___redArg(lean_object* v_v1_1606_, lean_object* v_v2_1607_){
_start:
{
uint8_t v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1608_ = 1;
v___x_1609_ = 6;
v___x_1610_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_1610_, 0, v_v1_1606_);
lean_ctor_set(v___x_1610_, 1, v_v2_1607_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*2, v___x_1609_);
v___x_1611_ = 1;
v___x_1612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*1, v___x_1611_);
v___x_1613_ = lp_kanon_Kanon_whenSome___redArg(v___x_1608_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__default(lean_object* v_O_1614_, lean_object* v_v1_1615_, lean_object* v_v2_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = lp_kanon__tiny__values_Tiny_sub_r__default___redArg(v_v1_1615_, v_v2_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_sub_r__default___boxed(lean_object* v_O_1618_, lean_object* v_v1_1619_, lean_object* v_v2_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = lp_kanon__tiny__values_Tiny_sub_r__default(v_O_1618_, v_v1_1619_, v_v2_1620_);
lean_dec_ref(v_O_1618_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero___redArg(lean_object* v_v1_1622_, lean_object* v_v2_1623_){
_start:
{
lean_object* v___y_1625_; lean_object* v_kind_1632_; 
v_kind_1632_ = lean_ctor_get(v_v1_1622_, 0);
if (lean_obj_tag(v_kind_1632_) == 6)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_a_1633_ = lean_ctor_get(v_kind_1632_, 0);
v___x_1634_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1635_ = lean_int_dec_eq(v_a_1633_, v___x_1634_);
v___x_1636_ = lp_kanon__tiny__values_Tiny_zero;
v___x_1637_ = lp_kanon_Kanon_whenSome___redArg(v___x_1635_, v___x_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
v___y_1625_ = v___x_1637_;
goto v___jp_1624_;
}
else
{
return v___x_1637_;
}
}
else
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_box(0);
v___y_1625_ = v___x_1638_;
goto v___jp_1624_;
}
v___jp_1624_:
{
lean_object* v_kind_1626_; 
v_kind_1626_ = lean_ctor_get(v_v2_1623_, 0);
if (lean_obj_tag(v_kind_1626_) == 6)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v___y_1625_);
v_a_1627_ = lean_ctor_get(v_kind_1626_, 0);
v___x_1628_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1629_ = lean_int_dec_eq(v_a_1627_, v___x_1628_);
v___x_1630_ = lp_kanon__tiny__values_Tiny_zero;
v___x_1631_ = lp_kanon_Kanon_whenSome___redArg(v___x_1629_, v___x_1630_);
return v___x_1631_;
}
else
{
return v___y_1625_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero___redArg___boxed(lean_object* v_v1_1639_, lean_object* v_v2_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = lp_kanon__tiny__values_Tiny_mul_r__zero___redArg(v_v1_1639_, v_v2_1640_);
lean_dec_ref(v_v2_1640_);
lean_dec_ref(v_v1_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero(lean_object* v_O_1642_, lean_object* v_v1_1643_, lean_object* v_v2_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lp_kanon__tiny__values_Tiny_mul_r__zero___redArg(v_v1_1643_, v_v2_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__zero___boxed(lean_object* v_O_1646_, lean_object* v_v1_1647_, lean_object* v_v2_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = lp_kanon__tiny__values_Tiny_mul_r__zero(v_O_1646_, v_v1_1647_, v_v2_1648_);
lean_dec_ref(v_v2_1648_);
lean_dec_ref(v_v1_1647_);
lean_dec_ref(v_O_1646_);
return v_res_1649_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_to_int(v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__one___redArg(lean_object* v_v1_1652_, lean_object* v_v2_1653_){
_start:
{
lean_object* v___y_1655_; lean_object* v_kind_1661_; 
v_kind_1661_ = lean_ctor_get(v_v1_1652_, 0);
if (lean_obj_tag(v_kind_1661_) == 6)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; lean_object* v___x_1665_; 
v_a_1662_ = lean_ctor_get(v_kind_1661_, 0);
v___x_1663_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0, &lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0);
v___x_1664_ = lean_int_dec_eq(v_a_1662_, v___x_1663_);
lean_inc_ref(v_v2_1653_);
v___x_1665_ = lp_kanon_Kanon_whenSome___redArg(v___x_1664_, v_v2_1653_);
if (lean_obj_tag(v___x_1665_) == 0)
{
v___y_1655_ = v___x_1665_;
goto v___jp_1654_;
}
else
{
lean_dec_ref(v_v2_1653_);
lean_dec_ref(v_v1_1652_);
return v___x_1665_;
}
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_box(0);
v___y_1655_ = v___x_1666_;
goto v___jp_1654_;
}
v___jp_1654_:
{
lean_object* v_kind_1656_; 
v_kind_1656_ = lean_ctor_get(v_v2_1653_, 0);
lean_inc_ref(v_kind_1656_);
lean_dec_ref(v_v2_1653_);
if (lean_obj_tag(v_kind_1656_) == 6)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v___y_1655_);
v_a_1657_ = lean_ctor_get(v_kind_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v_kind_1656_, 1);
v___x_1658_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0, &lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0);
v___x_1659_ = lean_int_dec_eq(v_a_1657_, v___x_1658_);
lean_dec(v_a_1657_);
v___x_1660_ = lp_kanon_Kanon_whenSome___redArg(v___x_1659_, v_v1_1652_);
return v___x_1660_;
}
else
{
lean_dec_ref(v_kind_1656_);
lean_dec_ref(v_v1_1652_);
return v___y_1655_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__one(lean_object* v_O_1667_, lean_object* v_v1_1668_, lean_object* v_v2_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = lp_kanon__tiny__values_Tiny_mul_r__one___redArg(v_v1_1668_, v_v2_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__one___boxed(lean_object* v_O_1671_, lean_object* v_v1_1672_, lean_object* v_v2_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = lp_kanon__tiny__values_Tiny_mul_r__one(v_O_1671_, v_v1_1672_, v_v2_1673_);
lean_dec_ref(v_O_1671_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits___redArg(lean_object* v_v1_1675_, lean_object* v_v2_1676_){
_start:
{
lean_object* v_kind_1677_; 
v_kind_1677_ = lean_ctor_get(v_v1_1675_, 0);
if (lean_obj_tag(v_kind_1677_) == 6)
{
lean_object* v_kind_1678_; 
v_kind_1678_ = lean_ctor_get(v_v2_1676_, 0);
if (lean_obj_tag(v_kind_1678_) == 6)
{
lean_object* v_a_1679_; lean_object* v_a_1680_; uint8_t v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_a_1679_ = lean_ctor_get(v_kind_1677_, 0);
v_a_1680_ = lean_ctor_get(v_kind_1678_, 0);
v___x_1681_ = 1;
v___x_1682_ = lean_int_mul(v_a_1679_, v_a_1680_);
v___x_1683_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1682_);
v___x_1684_ = lp_kanon_Kanon_whenSome___redArg(v___x_1681_, v___x_1683_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_box(0);
return v___x_1685_;
}
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_box(0);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits___redArg___boxed(lean_object* v_v1_1687_, lean_object* v_v2_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = lp_kanon__tiny__values_Tiny_mul_r__lits___redArg(v_v1_1687_, v_v2_1688_);
lean_dec_ref(v_v2_1688_);
lean_dec_ref(v_v1_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits(lean_object* v_O_1690_, lean_object* v_v1_1691_, lean_object* v_v2_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = lp_kanon__tiny__values_Tiny_mul_r__lits___redArg(v_v1_1691_, v_v2_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__lits___boxed(lean_object* v_O_1694_, lean_object* v_v1_1695_, lean_object* v_v2_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = lp_kanon__tiny__values_Tiny_mul_r__lits(v_O_1694_, v_v1_1695_, v_v2_1696_);
lean_dec_ref(v_v2_1696_);
lean_dec_ref(v_v1_1695_);
lean_dec_ref(v_O_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_r__default(lean_object* v_O_1698_, lean_object* v_v1_1699_, lean_object* v_v2_1700_){
_start:
{
uint8_t v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1701_ = 1;
v___x_1702_ = 7;
v___x_1703_ = lp_kanon__tiny__values_Tiny_mk__commut__binop(v_O_1698_, v___x_1702_, v_v1_1699_, v_v2_1700_);
v___x_1704_ = 1;
v___x_1705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*1, v___x_1704_);
v___x_1706_ = lp_kanon_Kanon_whenSome___redArg(v___x_1701_, v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mul_step(lean_object* v_O_1707_, lean_object* v_v1_1708_, lean_object* v_v2_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1710_ = lp_kanon__tiny__values_Tiny_mul_r__zero___redArg(v_v1_1708_, v_v2_1709_);
lean_inc_ref_n(v_v2_1709_, 2);
lean_inc_ref_n(v_v1_1708_, 2);
v___x_1711_ = lp_kanon__tiny__values_Tiny_mul_r__one___redArg(v_v1_1708_, v_v2_1709_);
v___x_1712_ = lp_kanon__tiny__values_Tiny_mul_r__lits___redArg(v_v1_1708_, v_v2_1709_);
v___x_1713_ = lp_kanon__tiny__values_Tiny_mul_r__default(v_O_1707_, v_v1_1708_, v_v2_1709_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1712_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1711_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1710_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lp_kanon_Kanon_firstSome___redArg(v___x_1718_);
lean_dec_ref_known(v___x_1718_, 2);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lp_kanon__tiny__values_Tiny_mul_spec(v_v1_1708_, v_v2_1709_);
return v___x_1720_;
}
else
{
lean_object* v_val_1721_; 
lean_dec_ref(v_v2_1709_);
lean_dec_ref(v_v1_1708_);
v_val_1721_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1721_);
lean_dec_ref_known(v___x_1719_, 1);
return v_val_1721_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one___redArg(lean_object* v_v1_1722_, lean_object* v_v2_1723_){
_start:
{
lean_object* v_kind_1724_; 
v_kind_1724_ = lean_ctor_get(v_v2_1723_, 0);
if (lean_obj_tag(v_kind_1724_) == 6)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v_a_1725_ = lean_ctor_get(v_kind_1724_, 0);
v___x_1726_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0, &lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0);
v___x_1727_ = lean_int_dec_eq(v_a_1725_, v___x_1726_);
v___x_1728_ = lp_kanon_Kanon_whenSome___redArg(v___x_1727_, v_v1_1722_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; 
lean_dec_ref(v_v1_1722_);
v___x_1729_ = lean_box(0);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one___redArg___boxed(lean_object* v_v1_1730_, lean_object* v_v2_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = lp_kanon__tiny__values_Tiny_div_r__one___redArg(v_v1_1730_, v_v2_1731_);
lean_dec_ref(v_v2_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one(lean_object* v_O_1733_, lean_object* v_v1_1734_, lean_object* v_v2_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = lp_kanon__tiny__values_Tiny_div_r__one___redArg(v_v1_1734_, v_v2_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__one___boxed(lean_object* v_O_1737_, lean_object* v_v1_1738_, lean_object* v_v2_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = lp_kanon__tiny__values_Tiny_div_r__one(v_O_1737_, v_v1_1738_, v_v2_1739_);
lean_dec_ref(v_v2_1739_);
lean_dec_ref(v_O_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits___redArg(lean_object* v_v1_1741_, lean_object* v_v2_1742_){
_start:
{
lean_object* v_kind_1743_; 
v_kind_1743_ = lean_ctor_get(v_v1_1741_, 0);
if (lean_obj_tag(v_kind_1743_) == 6)
{
lean_object* v_kind_1744_; 
v_kind_1744_ = lean_ctor_get(v_v2_1742_, 0);
if (lean_obj_tag(v_kind_1744_) == 6)
{
lean_object* v_a_1745_; lean_object* v_a_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_a_1745_ = lean_ctor_get(v_kind_1743_, 0);
v_a_1746_ = lean_ctor_get(v_kind_1744_, 0);
v___x_1747_ = 1;
v___x_1748_ = lean_int_ediv(v_a_1745_, v_a_1746_);
v___x_1749_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1748_);
v___x_1750_ = lp_kanon_Kanon_whenSome___redArg(v___x_1747_, v___x_1749_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_box(0);
return v___x_1751_;
}
}
else
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits___redArg___boxed(lean_object* v_v1_1753_, lean_object* v_v2_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = lp_kanon__tiny__values_Tiny_div_r__lits___redArg(v_v1_1753_, v_v2_1754_);
lean_dec_ref(v_v2_1754_);
lean_dec_ref(v_v1_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits(lean_object* v_O_1756_, lean_object* v_v1_1757_, lean_object* v_v2_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = lp_kanon__tiny__values_Tiny_div_r__lits___redArg(v_v1_1757_, v_v2_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__lits___boxed(lean_object* v_O_1760_, lean_object* v_v1_1761_, lean_object* v_v2_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = lp_kanon__tiny__values_Tiny_div_r__lits(v_O_1760_, v_v1_1761_, v_v2_1762_);
lean_dec_ref(v_v2_1762_);
lean_dec_ref(v_v1_1761_);
lean_dec_ref(v_O_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul___redArg(lean_object* v_v1_1764_, lean_object* v_v2_1765_){
_start:
{
lean_object* v_kind_1766_; lean_object* v___y_1768_; 
v_kind_1766_ = lean_ctor_get(v_v1_1764_, 0);
lean_inc_ref(v_kind_1766_);
lean_dec_ref(v_v1_1764_);
if (lean_obj_tag(v_kind_1766_) == 2)
{
uint8_t v_a_1778_; 
v_a_1778_ = lean_ctor_get_uint8(v_kind_1766_, sizeof(void*)*2);
if (v_a_1778_ == 7)
{
lean_object* v_a_1779_; lean_object* v_kind_1780_; 
v_a_1779_ = lean_ctor_get(v_kind_1766_, 1);
v_kind_1780_ = lean_ctor_get(v_a_1779_, 0);
if (lean_obj_tag(v_kind_1780_) == 6)
{
lean_object* v_kind_1781_; 
v_kind_1781_ = lean_ctor_get(v_v2_1765_, 0);
if (lean_obj_tag(v_kind_1781_) == 6)
{
lean_object* v_a_1782_; lean_object* v_a_1783_; lean_object* v_a_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; 
v_a_1782_ = lean_ctor_get(v_kind_1766_, 0);
v_a_1783_ = lean_ctor_get(v_kind_1780_, 0);
v_a_1784_ = lean_ctor_get(v_kind_1781_, 0);
v___x_1785_ = lean_int_dec_eq(v_a_1783_, v_a_1784_);
lean_inc_ref(v_a_1782_);
v___x_1786_ = lp_kanon_Kanon_whenSome___redArg(v___x_1785_, v_a_1782_);
if (lean_obj_tag(v___x_1786_) == 0)
{
v___y_1768_ = v___x_1786_;
goto v___jp_1767_;
}
else
{
lean_dec_ref_known(v_kind_1766_, 2);
return v___x_1786_;
}
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_box(0);
v___y_1768_ = v___x_1787_;
goto v___jp_1767_;
}
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_box(0);
v___y_1768_ = v___x_1788_;
goto v___jp_1767_;
}
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_box(0);
v___y_1768_ = v___x_1789_;
goto v___jp_1767_;
}
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_box(0);
v___y_1768_ = v___x_1790_;
goto v___jp_1767_;
}
v___jp_1767_:
{
if (lean_obj_tag(v_kind_1766_) == 2)
{
uint8_t v_a_1769_; 
v_a_1769_ = lean_ctor_get_uint8(v_kind_1766_, sizeof(void*)*2);
if (v_a_1769_ == 7)
{
lean_object* v_a_1770_; lean_object* v_kind_1771_; 
v_a_1770_ = lean_ctor_get(v_kind_1766_, 0);
v_kind_1771_ = lean_ctor_get(v_a_1770_, 0);
lean_inc_ref(v_kind_1771_);
if (lean_obj_tag(v_kind_1771_) == 6)
{
lean_object* v_kind_1772_; 
v_kind_1772_ = lean_ctor_get(v_v2_1765_, 0);
if (lean_obj_tag(v_kind_1772_) == 6)
{
lean_object* v_a_1773_; lean_object* v_a_1774_; lean_object* v_a_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v___y_1768_);
v_a_1773_ = lean_ctor_get(v_kind_1766_, 1);
lean_inc_ref(v_a_1773_);
lean_dec_ref_known(v_kind_1766_, 2);
v_a_1774_ = lean_ctor_get(v_kind_1771_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v_kind_1771_, 1);
v_a_1775_ = lean_ctor_get(v_kind_1772_, 0);
v___x_1776_ = lean_int_dec_eq(v_a_1774_, v_a_1775_);
lean_dec(v_a_1774_);
v___x_1777_ = lp_kanon_Kanon_whenSome___redArg(v___x_1776_, v_a_1773_);
return v___x_1777_;
}
else
{
lean_dec_ref_known(v_kind_1771_, 1);
lean_dec_ref_known(v_kind_1766_, 2);
return v___y_1768_;
}
}
else
{
lean_dec_ref(v_kind_1771_);
lean_dec_ref_known(v_kind_1766_, 2);
return v___y_1768_;
}
}
else
{
lean_dec_ref_known(v_kind_1766_, 2);
return v___y_1768_;
}
}
else
{
lean_dec_ref(v_kind_1766_);
return v___y_1768_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul___redArg___boxed(lean_object* v_v1_1791_, lean_object* v_v2_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = lp_kanon__tiny__values_Tiny_div_r__mul___redArg(v_v1_1791_, v_v2_1792_);
lean_dec_ref(v_v2_1792_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul(lean_object* v_O_1794_, lean_object* v_v1_1795_, lean_object* v_v2_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = lp_kanon__tiny__values_Tiny_div_r__mul___redArg(v_v1_1795_, v_v2_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__mul___boxed(lean_object* v_O_1798_, lean_object* v_v1_1799_, lean_object* v_v2_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = lp_kanon__tiny__values_Tiny_div_r__mul(v_O_1798_, v_v1_1799_, v_v2_1800_);
lean_dec_ref(v_v2_1800_);
lean_dec_ref(v_O_1798_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__default___redArg(lean_object* v_v1_1802_, lean_object* v_v2_1803_){
_start:
{
uint8_t v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1804_ = 1;
v___x_1805_ = 8;
v___x_1806_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_1806_, 0, v_v1_1802_);
lean_ctor_set(v___x_1806_, 1, v_v2_1803_);
lean_ctor_set_uint8(v___x_1806_, sizeof(void*)*2, v___x_1805_);
v___x_1807_ = 1;
v___x_1808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*1, v___x_1807_);
v___x_1809_ = lp_kanon_Kanon_whenSome___redArg(v___x_1804_, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__default(lean_object* v_O_1810_, lean_object* v_v1_1811_, lean_object* v_v2_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = lp_kanon__tiny__values_Tiny_div_r__default___redArg(v_v1_1811_, v_v2_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_r__default___boxed(lean_object* v_O_1814_, lean_object* v_v1_1815_, lean_object* v_v2_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = lp_kanon__tiny__values_Tiny_div_r__default(v_O_1814_, v_v1_1815_, v_v2_1816_);
lean_dec_ref(v_O_1814_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_step___redArg(lean_object* v_v1_1818_, lean_object* v_v2_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_inc_ref_n(v_v1_1818_, 3);
v___x_1820_ = lp_kanon__tiny__values_Tiny_div_r__one___redArg(v_v1_1818_, v_v2_1819_);
v___x_1821_ = lp_kanon__tiny__values_Tiny_div_r__lits___redArg(v_v1_1818_, v_v2_1819_);
v___x_1822_ = lp_kanon__tiny__values_Tiny_div_r__mul___redArg(v_v1_1818_, v_v2_1819_);
lean_inc_ref(v_v2_1819_);
v___x_1823_ = lp_kanon__tiny__values_Tiny_div_r__default___redArg(v_v1_1818_, v_v2_1819_);
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1822_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1821_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1820_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lp_kanon_Kanon_firstSome___redArg(v___x_1828_);
lean_dec_ref_known(v___x_1828_, 2);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1830_; 
v___x_1830_ = lp_kanon__tiny__values_Tiny_div_spec(v_v1_1818_, v_v2_1819_);
return v___x_1830_;
}
else
{
lean_object* v_val_1831_; 
lean_dec_ref(v_v2_1819_);
lean_dec_ref(v_v1_1818_);
v_val_1831_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_val_1831_);
lean_dec_ref_known(v___x_1829_, 1);
return v_val_1831_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_step(lean_object* v_O_1832_, lean_object* v_v1_1833_, lean_object* v_v2_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lp_kanon__tiny__values_Tiny_div_step___redArg(v_v1_1833_, v_v2_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_div_step___boxed(lean_object* v_O_1836_, lean_object* v_v1_1837_, lean_object* v_v2_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = lp_kanon__tiny__values_Tiny_div_step(v_O_1836_, v_v1_1837_, v_v2_1838_);
lean_dec_ref(v_O_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one___redArg(lean_object* v_v2_1840_){
_start:
{
lean_object* v_kind_1841_; 
v_kind_1841_ = lean_ctor_get(v_v2_1840_, 0);
if (lean_obj_tag(v_kind_1841_) == 6)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1842_ = lean_ctor_get(v_kind_1841_, 0);
v___x_1843_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0, &lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0);
v___x_1844_ = lean_int_dec_eq(v_a_1842_, v___x_1843_);
v___x_1845_ = lp_kanon__tiny__values_Tiny_zero;
v___x_1846_ = lp_kanon_Kanon_whenSome___redArg(v___x_1844_, v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one___redArg___boxed(lean_object* v_v2_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = lp_kanon__tiny__values_Tiny_rem_r__one___redArg(v_v2_1848_);
lean_dec_ref(v_v2_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one(lean_object* v_O_1850_, lean_object* v_v1_1851_, lean_object* v_v2_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lp_kanon__tiny__values_Tiny_rem_r__one___redArg(v_v2_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__one___boxed(lean_object* v_O_1854_, lean_object* v_v1_1855_, lean_object* v_v2_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = lp_kanon__tiny__values_Tiny_rem_r__one(v_O_1854_, v_v1_1855_, v_v2_1856_);
lean_dec_ref(v_v2_1856_);
lean_dec_ref(v_v1_1855_);
lean_dec_ref(v_O_1854_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg(lean_object* v_v1_1858_, lean_object* v_v2_1859_){
_start:
{
lean_object* v_kind_1860_; 
v_kind_1860_ = lean_ctor_get(v_v2_1859_, 0);
if (lean_obj_tag(v_kind_1860_) == 6)
{
lean_object* v_a_1861_; uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1861_ = lean_ctor_get(v_kind_1860_, 0);
v___x_1862_ = lp_kanon__tiny__values_Tiny_is__mod(v_v1_1858_, v_a_1861_);
v___x_1863_ = lp_kanon__tiny__values_Tiny_zero;
v___x_1864_ = lp_kanon_Kanon_whenSome___redArg(v___x_1862_, v___x_1863_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_box(0);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg___boxed(lean_object* v_v1_1866_, lean_object* v_v2_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg(v_v1_1866_, v_v2_1867_);
lean_dec_ref(v_v2_1867_);
lean_dec_ref(v_v1_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple(lean_object* v_O_1869_, lean_object* v_v1_1870_, lean_object* v_v2_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg(v_v1_1870_, v_v2_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__multiple___boxed(lean_object* v_O_1873_, lean_object* v_v1_1874_, lean_object* v_v2_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = lp_kanon__tiny__values_Tiny_rem_r__multiple(v_O_1873_, v_v1_1874_, v_v2_1875_);
lean_dec_ref(v_v2_1875_);
lean_dec_ref(v_v1_1874_);
lean_dec_ref(v_O_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits___redArg(lean_object* v_v1_1877_, lean_object* v_v2_1878_){
_start:
{
lean_object* v_kind_1879_; 
v_kind_1879_ = lean_ctor_get(v_v1_1877_, 0);
if (lean_obj_tag(v_kind_1879_) == 6)
{
lean_object* v_kind_1880_; 
v_kind_1880_ = lean_ctor_get(v_v2_1878_, 0);
if (lean_obj_tag(v_kind_1880_) == 6)
{
lean_object* v_a_1881_; lean_object* v_a_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_a_1881_ = lean_ctor_get(v_kind_1879_, 0);
v_a_1882_ = lean_ctor_get(v_kind_1880_, 0);
v___x_1883_ = 1;
v___x_1884_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1885_ = lean_int_dec_lt(v_a_1882_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_int_emod(v_a_1881_, v_a_1882_);
v___x_1887_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1886_);
v___x_1888_ = lp_kanon_Kanon_whenSome___redArg(v___x_1883_, v___x_1887_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_int_emod(v_a_1881_, v_a_1882_);
v___x_1890_ = lean_int_neg(v___x_1889_);
lean_dec(v___x_1889_);
v___x_1891_ = lp_kanon__tiny__values_Tiny_int__z(v___x_1890_);
v___x_1892_ = lp_kanon_Kanon_whenSome___redArg(v___x_1883_, v___x_1891_);
return v___x_1892_;
}
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_box(0);
return v___x_1893_;
}
}
else
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_box(0);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits___redArg___boxed(lean_object* v_v1_1895_, lean_object* v_v2_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = lp_kanon__tiny__values_Tiny_rem_r__lits___redArg(v_v1_1895_, v_v2_1896_);
lean_dec_ref(v_v2_1896_);
lean_dec_ref(v_v1_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits(lean_object* v_O_1898_, lean_object* v_v1_1899_, lean_object* v_v2_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lp_kanon__tiny__values_Tiny_rem_r__lits___redArg(v_v1_1899_, v_v2_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__lits___boxed(lean_object* v_O_1902_, lean_object* v_v1_1903_, lean_object* v_v2_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = lp_kanon__tiny__values_Tiny_rem_r__lits(v_O_1902_, v_v1_1903_, v_v2_1904_);
lean_dec_ref(v_v2_1904_);
lean_dec_ref(v_v1_1903_);
lean_dec_ref(v_O_1902_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__mul(lean_object* v_O_1906_, lean_object* v_v1_1907_, lean_object* v_v2_1908_){
_start:
{
lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; lean_object* v_kind_1920_; lean_object* v___y_1922_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; uint8_t v___y_1941_; lean_object* v___y_1949_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; uint8_t v___y_1968_; lean_object* v___y_1976_; 
v_kind_1920_ = lean_ctor_get(v_v1_1907_, 0);
lean_inc_ref(v_kind_1920_);
lean_dec_ref(v_v1_1907_);
if (lean_obj_tag(v_kind_1920_) == 2)
{
uint8_t v_a_1991_; 
v_a_1991_ = lean_ctor_get_uint8(v_kind_1920_, sizeof(void*)*2);
if (v_a_1991_ == 7)
{
lean_object* v_a_1992_; lean_object* v_kind_1993_; 
v_a_1992_ = lean_ctor_get(v_kind_1920_, 1);
v_kind_1993_ = lean_ctor_get(v_a_1992_, 0);
if (lean_obj_tag(v_kind_1993_) == 6)
{
lean_object* v_kind_1994_; 
v_kind_1994_ = lean_ctor_get(v_v2_1908_, 0);
if (lean_obj_tag(v_kind_1994_) == 2)
{
lean_object* v_a_1995_; lean_object* v_a_1996_; uint8_t v_a_1997_; lean_object* v_a_1998_; lean_object* v_a_1999_; uint8_t v___y_2001_; 
v_a_1995_ = lean_ctor_get(v_kind_1920_, 0);
v_a_1996_ = lean_ctor_get(v_kind_1993_, 0);
v_a_1997_ = lean_ctor_get_uint8(v_kind_1994_, sizeof(void*)*2);
v_a_1998_ = lean_ctor_get(v_kind_1994_, 0);
v_a_1999_ = lean_ctor_get(v_kind_1994_, 1);
if (v_a_1997_ == 7)
{
lean_object* v_kind_2008_; 
v_kind_2008_ = lean_ctor_get(v_a_1999_, 0);
if (lean_obj_tag(v_kind_2008_) == 6)
{
lean_object* v_a_2009_; uint8_t v___x_2010_; 
v_a_2009_ = lean_ctor_get(v_kind_2008_, 0);
v___x_2010_ = lean_int_dec_eq(v_a_1996_, v_a_2009_);
if (v___x_2010_ == 0)
{
v___y_2001_ = v___x_2010_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_2012_ = lean_int_dec_lt(v___x_2011_, v_a_1996_);
v___y_2001_ = v___x_2012_;
goto v___jp_2000_;
}
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_box(0);
v___y_1976_ = v___x_2013_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_box(0);
v___y_1976_ = v___x_2014_;
goto v___jp_1975_;
}
v___jp_2000_:
{
lean_object* v_mul_2002_; lean_object* v_rem_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_mul_2002_ = lean_ctor_get(v_O_1906_, 10);
v_rem_2003_ = lean_ctor_get(v_O_1906_, 12);
lean_inc(v_a_1996_);
v___x_2004_ = lp_kanon__tiny__values_Tiny_int__z(v_a_1996_);
lean_inc_ref(v_rem_2003_);
lean_inc_ref(v_a_1998_);
lean_inc_ref(v_a_1995_);
v___x_2005_ = lean_apply_2(v_rem_2003_, v_a_1995_, v_a_1998_);
lean_inc_ref(v_mul_2002_);
v___x_2006_ = lean_apply_2(v_mul_2002_, v___x_2004_, v___x_2005_);
v___x_2007_ = lp_kanon_Kanon_whenSome___redArg(v___y_2001_, v___x_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
v___y_1976_ = v___x_2007_;
goto v___jp_1975_;
}
else
{
lean_dec_ref_known(v_kind_1920_, 2);
lean_dec_ref(v_v2_1908_);
lean_dec_ref(v_O_1906_);
return v___x_2007_;
}
}
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_box(0);
v___y_1976_ = v___x_2015_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_box(0);
v___y_1976_ = v___x_2016_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_box(0);
v___y_1976_ = v___x_2017_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_box(0);
v___y_1976_ = v___x_2018_;
goto v___jp_1975_;
}
v___jp_1909_:
{
lean_object* v_mul_1914_; lean_object* v_rem_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_mul_1914_ = lean_ctor_get(v_O_1906_, 10);
lean_inc_ref(v_mul_1914_);
v_rem_1915_ = lean_ctor_get(v_O_1906_, 12);
lean_inc_ref(v_rem_1915_);
lean_dec_ref(v_O_1906_);
v___x_1916_ = lp_kanon__tiny__values_Tiny_int__z(v___y_1912_);
v___x_1917_ = lean_apply_2(v_rem_1915_, v___y_1910_, v___y_1911_);
v___x_1918_ = lean_apply_2(v_mul_1914_, v___x_1916_, v___x_1917_);
v___x_1919_ = lp_kanon_Kanon_whenSome___redArg(v___y_1913_, v___x_1918_);
return v___x_1919_;
}
v___jp_1921_:
{
if (lean_obj_tag(v_kind_1920_) == 2)
{
uint8_t v_a_1923_; 
v_a_1923_ = lean_ctor_get_uint8(v_kind_1920_, sizeof(void*)*2);
if (v_a_1923_ == 7)
{
lean_object* v_a_1924_; lean_object* v_kind_1925_; 
v_a_1924_ = lean_ctor_get(v_kind_1920_, 0);
v_kind_1925_ = lean_ctor_get(v_a_1924_, 0);
lean_inc_ref(v_kind_1925_);
if (lean_obj_tag(v_kind_1925_) == 6)
{
lean_object* v_kind_1926_; 
v_kind_1926_ = lean_ctor_get(v_v2_1908_, 0);
lean_inc_ref(v_kind_1926_);
lean_dec_ref(v_v2_1908_);
if (lean_obj_tag(v_kind_1926_) == 2)
{
uint8_t v_a_1927_; 
v_a_1927_ = lean_ctor_get_uint8(v_kind_1926_, sizeof(void*)*2);
if (v_a_1927_ == 7)
{
lean_object* v_a_1928_; lean_object* v_kind_1929_; 
v_a_1928_ = lean_ctor_get(v_kind_1926_, 0);
v_kind_1929_ = lean_ctor_get(v_a_1928_, 0);
lean_inc_ref(v_kind_1929_);
if (lean_obj_tag(v_kind_1929_) == 6)
{
lean_object* v_a_1930_; lean_object* v_a_1931_; lean_object* v_a_1932_; lean_object* v_a_1933_; uint8_t v___x_1934_; 
lean_dec(v___y_1922_);
v_a_1930_ = lean_ctor_get(v_kind_1920_, 1);
lean_inc_ref(v_a_1930_);
lean_dec_ref_known(v_kind_1920_, 2);
v_a_1931_ = lean_ctor_get(v_kind_1925_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v_kind_1925_, 1);
v_a_1932_ = lean_ctor_get(v_kind_1926_, 1);
lean_inc_ref(v_a_1932_);
lean_dec_ref_known(v_kind_1926_, 2);
v_a_1933_ = lean_ctor_get(v_kind_1929_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v_kind_1929_, 1);
v___x_1934_ = lean_int_dec_eq(v_a_1931_, v_a_1933_);
lean_dec(v_a_1933_);
if (v___x_1934_ == 0)
{
v___y_1910_ = v_a_1930_;
v___y_1911_ = v_a_1932_;
v___y_1912_ = v_a_1931_;
v___y_1913_ = v___x_1934_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1936_ = lean_int_dec_lt(v___x_1935_, v_a_1931_);
v___y_1910_ = v_a_1930_;
v___y_1911_ = v_a_1932_;
v___y_1912_ = v_a_1931_;
v___y_1913_ = v___x_1936_;
goto v___jp_1909_;
}
}
else
{
lean_dec_ref(v_kind_1929_);
lean_dec_ref_known(v_kind_1926_, 2);
lean_dec_ref_known(v_kind_1925_, 1);
lean_dec_ref_known(v_kind_1920_, 2);
lean_dec_ref(v_O_1906_);
return v___y_1922_;
}
}
else
{
lean_dec_ref_known(v_kind_1926_, 2);
lean_dec_ref_known(v_kind_1925_, 1);
lean_dec_ref_known(v_kind_1920_, 2);
lean_dec_ref(v_O_1906_);
return v___y_1922_;
}
}
else
{
lean_dec_ref(v_kind_1926_);
lean_dec_ref_known(v_kind_1925_, 1);
lean_dec_ref_known(v_kind_1920_, 2);
lean_dec_ref(v_O_1906_);
return v___y_1922_;
}
}
else
{
lean_dec_ref(v_kind_1925_);
lean_dec_ref_known(v_kind_1920_, 2);
lean_dec_ref(v_v2_1908_);
lean_dec_ref(v_O_1906_);
return v___y_1922_;
}
}
else
{
lean_dec_ref_known(v_kind_1920_, 2);
lean_dec_ref(v_v2_1908_);
lean_dec_ref(v_O_1906_);
return v___y_1922_;
}
}
else
{
lean_dec_ref(v_kind_1920_);
lean_dec_ref(v_v2_1908_);
lean_dec_ref(v_O_1906_);
return v___y_1922_;
}
}
v___jp_1937_:
{
lean_object* v_mul_1942_; lean_object* v_rem_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_mul_1942_ = lean_ctor_get(v_O_1906_, 10);
v_rem_1943_ = lean_ctor_get(v_O_1906_, 12);
v___x_1944_ = lp_kanon__tiny__values_Tiny_int__z(v___y_1940_);
lean_inc_ref(v_rem_1943_);
v___x_1945_ = lean_apply_2(v_rem_1943_, v___y_1938_, v___y_1939_);
lean_inc_ref(v_mul_1942_);
v___x_1946_ = lean_apply_2(v_mul_1942_, v___x_1944_, v___x_1945_);
v___x_1947_ = lp_kanon_Kanon_whenSome___redArg(v___y_1941_, v___x_1946_);
if (lean_obj_tag(v___x_1947_) == 0)
{
v___y_1922_ = v___x_1947_;
goto v___jp_1921_;
}
else
{
lean_dec_ref(v_kind_1920_);
lean_dec_ref(v_v2_1908_);
lean_dec_ref(v_O_1906_);
return v___x_1947_;
}
}
v___jp_1948_:
{
if (lean_obj_tag(v_kind_1920_) == 2)
{
uint8_t v_a_1950_; 
v_a_1950_ = lean_ctor_get_uint8(v_kind_1920_, sizeof(void*)*2);
if (v_a_1950_ == 7)
{
lean_object* v_a_1951_; lean_object* v_kind_1952_; 
v_a_1951_ = lean_ctor_get(v_kind_1920_, 0);
v_kind_1952_ = lean_ctor_get(v_a_1951_, 0);
if (lean_obj_tag(v_kind_1952_) == 6)
{
lean_object* v_kind_1953_; 
v_kind_1953_ = lean_ctor_get(v_v2_1908_, 0);
if (lean_obj_tag(v_kind_1953_) == 2)
{
uint8_t v_a_1954_; 
v_a_1954_ = lean_ctor_get_uint8(v_kind_1953_, sizeof(void*)*2);
if (v_a_1954_ == 7)
{
lean_object* v_a_1955_; lean_object* v_kind_1956_; 
v_a_1955_ = lean_ctor_get(v_kind_1953_, 1);
v_kind_1956_ = lean_ctor_get(v_a_1955_, 0);
if (lean_obj_tag(v_kind_1956_) == 6)
{
lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v_a_1959_; lean_object* v_a_1960_; uint8_t v___x_1961_; 
lean_dec(v___y_1949_);
v_a_1957_ = lean_ctor_get(v_kind_1920_, 1);
v_a_1958_ = lean_ctor_get(v_kind_1952_, 0);
v_a_1959_ = lean_ctor_get(v_kind_1953_, 0);
v_a_1960_ = lean_ctor_get(v_kind_1956_, 0);
v___x_1961_ = lean_int_dec_eq(v_a_1958_, v_a_1960_);
if (v___x_1961_ == 0)
{
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1959_);
lean_inc_ref(v_a_1957_);
v___y_1938_ = v_a_1957_;
v___y_1939_ = v_a_1959_;
v___y_1940_ = v_a_1958_;
v___y_1941_ = v___x_1961_;
goto v___jp_1937_;
}
else
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1963_ = lean_int_dec_lt(v___x_1962_, v_a_1958_);
lean_inc(v_a_1958_);
lean_inc_ref(v_a_1959_);
lean_inc_ref(v_a_1957_);
v___y_1938_ = v_a_1957_;
v___y_1939_ = v_a_1959_;
v___y_1940_ = v_a_1958_;
v___y_1941_ = v___x_1963_;
goto v___jp_1937_;
}
}
else
{
v___y_1922_ = v___y_1949_;
goto v___jp_1921_;
}
}
else
{
v___y_1922_ = v___y_1949_;
goto v___jp_1921_;
}
}
else
{
v___y_1922_ = v___y_1949_;
goto v___jp_1921_;
}
}
else
{
v___y_1922_ = v___y_1949_;
goto v___jp_1921_;
}
}
else
{
v___y_1922_ = v___y_1949_;
goto v___jp_1921_;
}
}
else
{
v___y_1922_ = v___y_1949_;
goto v___jp_1921_;
}
}
v___jp_1964_:
{
lean_object* v_mul_1969_; lean_object* v_rem_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_mul_1969_ = lean_ctor_get(v_O_1906_, 10);
v_rem_1970_ = lean_ctor_get(v_O_1906_, 12);
v___x_1971_ = lp_kanon__tiny__values_Tiny_int__z(v___y_1967_);
lean_inc_ref(v_rem_1970_);
v___x_1972_ = lean_apply_2(v_rem_1970_, v___y_1965_, v___y_1966_);
lean_inc_ref(v_mul_1969_);
v___x_1973_ = lean_apply_2(v_mul_1969_, v___x_1971_, v___x_1972_);
v___x_1974_ = lp_kanon_Kanon_whenSome___redArg(v___y_1968_, v___x_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
v___y_1949_ = v___x_1974_;
goto v___jp_1948_;
}
else
{
lean_dec_ref(v_kind_1920_);
lean_dec_ref(v_v2_1908_);
lean_dec_ref(v_O_1906_);
return v___x_1974_;
}
}
v___jp_1975_:
{
if (lean_obj_tag(v_kind_1920_) == 2)
{
uint8_t v_a_1977_; 
v_a_1977_ = lean_ctor_get_uint8(v_kind_1920_, sizeof(void*)*2);
if (v_a_1977_ == 7)
{
lean_object* v_a_1978_; lean_object* v_kind_1979_; 
v_a_1978_ = lean_ctor_get(v_kind_1920_, 1);
v_kind_1979_ = lean_ctor_get(v_a_1978_, 0);
if (lean_obj_tag(v_kind_1979_) == 6)
{
lean_object* v_kind_1980_; 
v_kind_1980_ = lean_ctor_get(v_v2_1908_, 0);
if (lean_obj_tag(v_kind_1980_) == 2)
{
uint8_t v_a_1981_; 
v_a_1981_ = lean_ctor_get_uint8(v_kind_1980_, sizeof(void*)*2);
if (v_a_1981_ == 7)
{
lean_object* v_a_1982_; lean_object* v_kind_1983_; 
v_a_1982_ = lean_ctor_get(v_kind_1980_, 0);
v_kind_1983_ = lean_ctor_get(v_a_1982_, 0);
if (lean_obj_tag(v_kind_1983_) == 6)
{
lean_object* v_a_1984_; lean_object* v_a_1985_; lean_object* v_a_1986_; lean_object* v_a_1987_; uint8_t v___x_1988_; 
lean_dec(v___y_1976_);
v_a_1984_ = lean_ctor_get(v_kind_1920_, 0);
v_a_1985_ = lean_ctor_get(v_kind_1979_, 0);
v_a_1986_ = lean_ctor_get(v_kind_1980_, 1);
v_a_1987_ = lean_ctor_get(v_kind_1983_, 0);
v___x_1988_ = lean_int_dec_eq(v_a_1985_, v_a_1987_);
if (v___x_1988_ == 0)
{
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1986_);
lean_inc_ref(v_a_1984_);
v___y_1965_ = v_a_1984_;
v___y_1966_ = v_a_1986_;
v___y_1967_ = v_a_1985_;
v___y_1968_ = v___x_1988_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_1990_ = lean_int_dec_lt(v___x_1989_, v_a_1985_);
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1986_);
lean_inc_ref(v_a_1984_);
v___y_1965_ = v_a_1984_;
v___y_1966_ = v_a_1986_;
v___y_1967_ = v_a_1985_;
v___y_1968_ = v___x_1990_;
goto v___jp_1964_;
}
}
else
{
v___y_1949_ = v___y_1976_;
goto v___jp_1948_;
}
}
else
{
v___y_1949_ = v___y_1976_;
goto v___jp_1948_;
}
}
else
{
v___y_1949_ = v___y_1976_;
goto v___jp_1948_;
}
}
else
{
v___y_1949_ = v___y_1976_;
goto v___jp_1948_;
}
}
else
{
v___y_1949_ = v___y_1976_;
goto v___jp_1948_;
}
}
else
{
v___y_1949_ = v___y_1976_;
goto v___jp_1948_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__default___redArg(lean_object* v_v1_2019_, lean_object* v_v2_2020_){
_start:
{
uint8_t v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2021_ = 1;
v___x_2022_ = 9;
v___x_2023_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2023_, 0, v_v1_2019_);
lean_ctor_set(v___x_2023_, 1, v_v2_2020_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*2, v___x_2022_);
v___x_2024_ = 1;
v___x_2025_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*1, v___x_2024_);
v___x_2026_ = lp_kanon_Kanon_whenSome___redArg(v___x_2021_, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__default(lean_object* v_O_2027_, lean_object* v_v1_2028_, lean_object* v_v2_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = lp_kanon__tiny__values_Tiny_rem_r__default___redArg(v_v1_2028_, v_v2_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_r__default___boxed(lean_object* v_O_2031_, lean_object* v_v1_2032_, lean_object* v_v2_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = lp_kanon__tiny__values_Tiny_rem_r__default(v_O_2031_, v_v1_2032_, v_v2_2033_);
lean_dec_ref(v_O_2031_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_rem_step(lean_object* v_O_2035_, lean_object* v_v1_2036_, lean_object* v_v2_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2038_ = lp_kanon__tiny__values_Tiny_rem_r__one___redArg(v_v2_2037_);
v___x_2039_ = lp_kanon__tiny__values_Tiny_rem_r__multiple___redArg(v_v1_2036_, v_v2_2037_);
v___x_2040_ = lp_kanon__tiny__values_Tiny_rem_r__lits___redArg(v_v1_2036_, v_v2_2037_);
lean_inc_ref_n(v_v2_2037_, 2);
lean_inc_ref_n(v_v1_2036_, 2);
v___x_2041_ = lp_kanon__tiny__values_Tiny_rem_r__mul(v_O_2035_, v_v1_2036_, v_v2_2037_);
v___x_2042_ = lp_kanon__tiny__values_Tiny_rem_r__default___redArg(v_v1_2036_, v_v2_2037_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2041_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2040_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2039_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2038_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lp_kanon_Kanon_firstSome___redArg(v___x_2048_);
lean_dec_ref_known(v___x_2048_, 2);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lp_kanon__tiny__values_Tiny_rem_spec(v_v1_2036_, v_v2_2037_);
return v___x_2050_;
}
else
{
lean_object* v_val_2051_; 
lean_dec_ref(v_v2_2037_);
lean_dec_ref(v_v1_2036_);
v_val_2051_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2049_, 1);
return v_val_2051_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one___redArg(lean_object* v_v2_2052_){
_start:
{
lean_object* v_kind_2053_; 
v_kind_2053_ = lean_ctor_get(v_v2_2052_, 0);
if (lean_obj_tag(v_kind_2053_) == 6)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2054_ = lean_ctor_get(v_kind_2053_, 0);
v___x_2055_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0, &lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0_once, _init_lp_kanon__tiny__values_Tiny_mul_r__one___redArg___closed__0);
v___x_2056_ = lean_int_dec_eq(v_a_2054_, v___x_2055_);
v___x_2057_ = lp_kanon__tiny__values_Tiny_zero;
v___x_2058_ = lp_kanon_Kanon_whenSome___redArg(v___x_2056_, v___x_2057_);
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_box(0);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one___redArg___boxed(lean_object* v_v2_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = lp_kanon__tiny__values_Tiny_mod___00r__one___redArg(v_v2_2060_);
lean_dec_ref(v_v2_2060_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one(lean_object* v_O_2062_, lean_object* v_v1_2063_, lean_object* v_v2_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = lp_kanon__tiny__values_Tiny_mod___00r__one___redArg(v_v2_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__one___boxed(lean_object* v_O_2066_, lean_object* v_v1_2067_, lean_object* v_v2_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = lp_kanon__tiny__values_Tiny_mod___00r__one(v_O_2066_, v_v1_2067_, v_v2_2068_);
lean_dec_ref(v_v2_2068_);
lean_dec_ref(v_v1_2067_);
lean_dec_ref(v_O_2066_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg(lean_object* v_v1_2070_, lean_object* v_v2_2071_){
_start:
{
lean_object* v_kind_2072_; 
v_kind_2072_ = lean_ctor_get(v_v2_2071_, 0);
if (lean_obj_tag(v_kind_2072_) == 6)
{
lean_object* v_a_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_a_2073_ = lean_ctor_get(v_kind_2072_, 0);
v___x_2074_ = lp_kanon__tiny__values_Tiny_is__mod(v_v1_2070_, v_a_2073_);
v___x_2075_ = lp_kanon__tiny__values_Tiny_zero;
v___x_2076_ = lp_kanon_Kanon_whenSome___redArg(v___x_2074_, v___x_2075_);
return v___x_2076_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_box(0);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg___boxed(lean_object* v_v1_2078_, lean_object* v_v2_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg(v_v1_2078_, v_v2_2079_);
lean_dec_ref(v_v2_2079_);
lean_dec_ref(v_v1_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple(lean_object* v_O_2081_, lean_object* v_v1_2082_, lean_object* v_v2_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg(v_v1_2082_, v_v2_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__multiple___boxed(lean_object* v_O_2085_, lean_object* v_v1_2086_, lean_object* v_v2_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = lp_kanon__tiny__values_Tiny_mod___00r__multiple(v_O_2085_, v_v1_2086_, v_v2_2087_);
lean_dec_ref(v_v2_2087_);
lean_dec_ref(v_v1_2086_);
lean_dec_ref(v_O_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg(lean_object* v_v1_2089_, lean_object* v_v2_2090_){
_start:
{
lean_object* v_kind_2091_; 
v_kind_2091_ = lean_ctor_get(v_v1_2089_, 0);
if (lean_obj_tag(v_kind_2091_) == 6)
{
lean_object* v_kind_2092_; 
v_kind_2092_ = lean_ctor_get(v_v2_2090_, 0);
if (lean_obj_tag(v_kind_2092_) == 6)
{
lean_object* v_a_2093_; lean_object* v_a_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2093_ = lean_ctor_get(v_kind_2091_, 0);
v_a_2094_ = lean_ctor_get(v_kind_2092_, 0);
v___x_2095_ = 1;
v___x_2096_ = lean_int_emod(v_a_2093_, v_a_2094_);
v___x_2097_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2096_);
v___x_2098_ = lp_kanon_Kanon_whenSome___redArg(v___x_2095_, v___x_2097_);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; 
v___x_2099_ = lean_box(0);
return v___x_2099_;
}
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_box(0);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg___boxed(lean_object* v_v1_2101_, lean_object* v_v2_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg(v_v1_2101_, v_v2_2102_);
lean_dec_ref(v_v2_2102_);
lean_dec_ref(v_v1_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits(lean_object* v_O_2104_, lean_object* v_v1_2105_, lean_object* v_v2_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg(v_v1_2105_, v_v2_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__lits___boxed(lean_object* v_O_2108_, lean_object* v_v1_2109_, lean_object* v_v2_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = lp_kanon__tiny__values_Tiny_mod___00r__lits(v_O_2108_, v_v1_2109_, v_v2_2110_);
lean_dec_ref(v_v2_2110_);
lean_dec_ref(v_v1_2109_);
lean_dec_ref(v_O_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__mod__mod(lean_object* v_O_2112_, lean_object* v_v1_2113_, lean_object* v_v2_2114_){
_start:
{
lean_object* v_kind_2115_; 
v_kind_2115_ = lean_ctor_get(v_v1_2113_, 0);
lean_inc_ref(v_kind_2115_);
lean_dec_ref(v_v1_2113_);
if (lean_obj_tag(v_kind_2115_) == 2)
{
uint8_t v_a_2116_; lean_object* v_a_2117_; lean_object* v_a_2118_; uint8_t v___y_2120_; 
v_a_2116_ = lean_ctor_get_uint8(v_kind_2115_, sizeof(void*)*2);
v_a_2117_ = lean_ctor_get(v_kind_2115_, 0);
lean_inc_ref(v_a_2117_);
v_a_2118_ = lean_ctor_get(v_kind_2115_, 1);
lean_inc_ref(v_a_2118_);
lean_dec_ref_known(v_kind_2115_, 2);
if (v_a_2116_ == 10)
{
lean_object* v_kind_2124_; 
v_kind_2124_ = lean_ctor_get(v_a_2118_, 0);
lean_inc_ref(v_kind_2124_);
lean_dec_ref(v_a_2118_);
if (lean_obj_tag(v_kind_2124_) == 6)
{
lean_object* v_kind_2125_; 
v_kind_2125_ = lean_ctor_get(v_v2_2114_, 0);
if (lean_obj_tag(v_kind_2125_) == 6)
{
lean_object* v_a_2126_; lean_object* v_a_2127_; uint8_t v___x_2128_; 
v_a_2126_ = lean_ctor_get(v_kind_2124_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v_kind_2124_, 1);
v_a_2127_ = lean_ctor_get(v_kind_2125_, 0);
v___x_2128_ = lean_int_dec_le(v_a_2127_, v_a_2126_);
if (v___x_2128_ == 0)
{
lean_dec(v_a_2126_);
v___y_2120_ = v___x_2128_;
goto v___jp_2119_;
}
else
{
uint8_t v___x_2129_; 
v___x_2129_ = l_Int_decidableDvd(v_a_2127_, v_a_2126_);
lean_dec(v_a_2126_);
v___y_2120_ = v___x_2129_;
goto v___jp_2119_;
}
}
else
{
lean_object* v___x_2130_; 
lean_dec_ref_known(v_kind_2124_, 1);
lean_dec_ref(v_a_2117_);
lean_dec_ref(v_v2_2114_);
lean_dec_ref(v_O_2112_);
v___x_2130_ = lean_box(0);
return v___x_2130_;
}
}
else
{
lean_object* v___x_2131_; 
lean_dec_ref(v_kind_2124_);
lean_dec_ref(v_a_2117_);
lean_dec_ref(v_v2_2114_);
lean_dec_ref(v_O_2112_);
v___x_2131_ = lean_box(0);
return v___x_2131_;
}
}
else
{
lean_object* v___x_2132_; 
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec_ref(v_v2_2114_);
lean_dec_ref(v_O_2112_);
v___x_2132_ = lean_box(0);
return v___x_2132_;
}
v___jp_2119_:
{
lean_object* v_mod___2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_mod___2121_ = lean_ctor_get(v_O_2112_, 13);
lean_inc_ref(v_mod___2121_);
lean_dec_ref(v_O_2112_);
v___x_2122_ = lean_apply_2(v_mod___2121_, v_a_2117_, v_v2_2114_);
v___x_2123_ = lp_kanon_Kanon_whenSome___redArg(v___y_2120_, v___x_2122_);
return v___x_2123_;
}
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v_kind_2115_);
lean_dec_ref(v_v2_2114_);
lean_dec_ref(v_O_2112_);
v___x_2133_ = lean_box(0);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__add__mod(lean_object* v_O_2134_, lean_object* v_v1_2135_, lean_object* v_v2_2136_){
_start:
{
lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v_kind_2146_; lean_object* v___y_2148_; 
v_kind_2146_ = lean_ctor_get(v_v1_2135_, 0);
lean_inc_ref(v_kind_2146_);
lean_dec_ref(v_v1_2135_);
if (lean_obj_tag(v_kind_2146_) == 2)
{
uint8_t v_a_2162_; 
v_a_2162_ = lean_ctor_get_uint8(v_kind_2146_, sizeof(void*)*2);
if (v_a_2162_ == 5)
{
lean_object* v_a_2163_; lean_object* v_kind_2164_; 
v_a_2163_ = lean_ctor_get(v_kind_2146_, 1);
v_kind_2164_ = lean_ctor_get(v_a_2163_, 0);
if (lean_obj_tag(v_kind_2164_) == 2)
{
lean_object* v_a_2165_; uint8_t v_a_2166_; lean_object* v_a_2167_; lean_object* v_a_2168_; uint8_t v___y_2170_; 
v_a_2165_ = lean_ctor_get(v_kind_2146_, 0);
v_a_2166_ = lean_ctor_get_uint8(v_kind_2164_, sizeof(void*)*2);
v_a_2167_ = lean_ctor_get(v_kind_2164_, 0);
v_a_2168_ = lean_ctor_get(v_kind_2164_, 1);
if (v_a_2166_ == 10)
{
lean_object* v_kind_2176_; 
v_kind_2176_ = lean_ctor_get(v_a_2168_, 0);
if (lean_obj_tag(v_kind_2176_) == 6)
{
lean_object* v_kind_2177_; 
v_kind_2177_ = lean_ctor_get(v_v2_2136_, 0);
if (lean_obj_tag(v_kind_2177_) == 6)
{
lean_object* v_a_2178_; lean_object* v_a_2179_; uint8_t v___x_2180_; 
v_a_2178_ = lean_ctor_get(v_kind_2176_, 0);
v_a_2179_ = lean_ctor_get(v_kind_2177_, 0);
v___x_2180_ = lean_int_dec_le(v_a_2179_, v_a_2178_);
if (v___x_2180_ == 0)
{
v___y_2170_ = v___x_2180_;
goto v___jp_2169_;
}
else
{
uint8_t v___x_2181_; 
v___x_2181_ = l_Int_decidableDvd(v_a_2179_, v_a_2178_);
v___y_2170_ = v___x_2181_;
goto v___jp_2169_;
}
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_box(0);
v___y_2148_ = v___x_2182_;
goto v___jp_2147_;
}
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_box(0);
v___y_2148_ = v___x_2183_;
goto v___jp_2147_;
}
}
else
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_box(0);
v___y_2148_ = v___x_2184_;
goto v___jp_2147_;
}
v___jp_2169_:
{
lean_object* v_add_2171_; lean_object* v_mod___2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_add_2171_ = lean_ctor_get(v_O_2134_, 8);
v_mod___2172_ = lean_ctor_get(v_O_2134_, 13);
lean_inc_ref(v_add_2171_);
lean_inc_ref(v_a_2167_);
lean_inc_ref(v_a_2165_);
v___x_2173_ = lean_apply_2(v_add_2171_, v_a_2165_, v_a_2167_);
lean_inc_ref(v_mod___2172_);
lean_inc_ref(v_v2_2136_);
v___x_2174_ = lean_apply_2(v_mod___2172_, v___x_2173_, v_v2_2136_);
v___x_2175_ = lp_kanon_Kanon_whenSome___redArg(v___y_2170_, v___x_2174_);
if (lean_obj_tag(v___x_2175_) == 0)
{
v___y_2148_ = v___x_2175_;
goto v___jp_2147_;
}
else
{
lean_dec_ref_known(v_kind_2146_, 2);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___x_2175_;
}
}
}
else
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_box(0);
v___y_2148_ = v___x_2185_;
goto v___jp_2147_;
}
}
else
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_box(0);
v___y_2148_ = v___x_2186_;
goto v___jp_2147_;
}
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_box(0);
v___y_2148_ = v___x_2187_;
goto v___jp_2147_;
}
v___jp_2137_:
{
lean_object* v_add_2141_; lean_object* v_mod___2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_add_2141_ = lean_ctor_get(v_O_2134_, 8);
lean_inc_ref(v_add_2141_);
v_mod___2142_ = lean_ctor_get(v_O_2134_, 13);
lean_inc_ref(v_mod___2142_);
lean_dec_ref(v_O_2134_);
v___x_2143_ = lean_apply_2(v_add_2141_, v___y_2138_, v___y_2139_);
v___x_2144_ = lean_apply_2(v_mod___2142_, v___x_2143_, v_v2_2136_);
v___x_2145_ = lp_kanon_Kanon_whenSome___redArg(v___y_2140_, v___x_2144_);
return v___x_2145_;
}
v___jp_2147_:
{
if (lean_obj_tag(v_kind_2146_) == 2)
{
uint8_t v_a_2149_; 
v_a_2149_ = lean_ctor_get_uint8(v_kind_2146_, sizeof(void*)*2);
if (v_a_2149_ == 5)
{
lean_object* v_a_2150_; lean_object* v_kind_2151_; 
v_a_2150_ = lean_ctor_get(v_kind_2146_, 0);
v_kind_2151_ = lean_ctor_get(v_a_2150_, 0);
lean_inc_ref(v_kind_2151_);
if (lean_obj_tag(v_kind_2151_) == 2)
{
uint8_t v_a_2152_; 
v_a_2152_ = lean_ctor_get_uint8(v_kind_2151_, sizeof(void*)*2);
if (v_a_2152_ == 10)
{
lean_object* v_a_2153_; lean_object* v_kind_2154_; 
v_a_2153_ = lean_ctor_get(v_kind_2151_, 1);
v_kind_2154_ = lean_ctor_get(v_a_2153_, 0);
lean_inc_ref(v_kind_2154_);
if (lean_obj_tag(v_kind_2154_) == 6)
{
lean_object* v_kind_2155_; 
v_kind_2155_ = lean_ctor_get(v_v2_2136_, 0);
if (lean_obj_tag(v_kind_2155_) == 6)
{
lean_object* v_a_2156_; lean_object* v_a_2157_; lean_object* v_a_2158_; lean_object* v_a_2159_; uint8_t v___x_2160_; 
lean_dec(v___y_2148_);
v_a_2156_ = lean_ctor_get(v_kind_2146_, 1);
lean_inc_ref(v_a_2156_);
lean_dec_ref_known(v_kind_2146_, 2);
v_a_2157_ = lean_ctor_get(v_kind_2151_, 0);
lean_inc_ref(v_a_2157_);
lean_dec_ref_known(v_kind_2151_, 2);
v_a_2158_ = lean_ctor_get(v_kind_2154_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v_kind_2154_, 1);
v_a_2159_ = lean_ctor_get(v_kind_2155_, 0);
v___x_2160_ = lean_int_dec_le(v_a_2159_, v_a_2158_);
if (v___x_2160_ == 0)
{
lean_dec(v_a_2158_);
v___y_2138_ = v_a_2156_;
v___y_2139_ = v_a_2157_;
v___y_2140_ = v___x_2160_;
goto v___jp_2137_;
}
else
{
uint8_t v___x_2161_; 
v___x_2161_ = l_Int_decidableDvd(v_a_2159_, v_a_2158_);
lean_dec(v_a_2158_);
v___y_2138_ = v_a_2156_;
v___y_2139_ = v_a_2157_;
v___y_2140_ = v___x_2161_;
goto v___jp_2137_;
}
}
else
{
lean_dec_ref_known(v_kind_2154_, 1);
lean_dec_ref_known(v_kind_2151_, 2);
lean_dec_ref_known(v_kind_2146_, 2);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___y_2148_;
}
}
else
{
lean_dec_ref(v_kind_2154_);
lean_dec_ref_known(v_kind_2151_, 2);
lean_dec_ref_known(v_kind_2146_, 2);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___y_2148_;
}
}
else
{
lean_dec_ref_known(v_kind_2151_, 2);
lean_dec_ref_known(v_kind_2146_, 2);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___y_2148_;
}
}
else
{
lean_dec_ref(v_kind_2151_);
lean_dec_ref_known(v_kind_2146_, 2);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___y_2148_;
}
}
else
{
lean_dec_ref_known(v_kind_2146_, 2);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___y_2148_;
}
}
else
{
lean_dec_ref(v_kind_2146_);
lean_dec_ref(v_v2_2136_);
lean_dec_ref(v_O_2134_);
return v___y_2148_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__default___redArg(lean_object* v_v1_2188_, lean_object* v_v2_2189_){
_start:
{
uint8_t v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2190_ = 1;
v___x_2191_ = 10;
v___x_2192_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2192_, 0, v_v1_2188_);
lean_ctor_set(v___x_2192_, 1, v_v2_2189_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*2, v___x_2191_);
v___x_2193_ = 1;
v___x_2194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*1, v___x_2193_);
v___x_2195_ = lp_kanon_Kanon_whenSome___redArg(v___x_2190_, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__default(lean_object* v_O_2196_, lean_object* v_v1_2197_, lean_object* v_v2_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = lp_kanon__tiny__values_Tiny_mod___00r__default___redArg(v_v1_2197_, v_v2_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00r__default___boxed(lean_object* v_O_2200_, lean_object* v_v1_2201_, lean_object* v_v2_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = lp_kanon__tiny__values_Tiny_mod___00r__default(v_O_2200_, v_v1_2201_, v_v2_2202_);
lean_dec_ref(v_O_2200_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_mod___00step(lean_object* v_O_2204_, lean_object* v_v1_2205_, lean_object* v_v2_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2207_ = lp_kanon__tiny__values_Tiny_mod___00r__one___redArg(v_v2_2206_);
v___x_2208_ = lp_kanon__tiny__values_Tiny_mod___00r__multiple___redArg(v_v1_2205_, v_v2_2206_);
v___x_2209_ = lp_kanon__tiny__values_Tiny_mod___00r__lits___redArg(v_v1_2205_, v_v2_2206_);
lean_inc_ref_n(v_v2_2206_, 3);
lean_inc_ref_n(v_v1_2205_, 3);
lean_inc_ref(v_O_2204_);
v___x_2210_ = lp_kanon__tiny__values_Tiny_mod___00r__mod__mod(v_O_2204_, v_v1_2205_, v_v2_2206_);
v___x_2211_ = lp_kanon__tiny__values_Tiny_mod___00r__add__mod(v_O_2204_, v_v1_2205_, v_v2_2206_);
v___x_2212_ = lp_kanon__tiny__values_Tiny_mod___00r__default___redArg(v_v1_2205_, v_v2_2206_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2211_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2210_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2209_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2208_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2207_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lp_kanon_Kanon_firstSome___redArg(v___x_2219_);
lean_dec_ref_known(v___x_2219_, 2);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
v___x_2221_ = lp_kanon__tiny__values_Tiny_mod___00spec(v_v1_2205_, v_v2_2206_);
return v___x_2221_;
}
else
{
lean_object* v_val_2222_; 
lean_dec_ref(v_v2_2206_);
lean_dec_ref(v_v1_2205_);
v_val_2222_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_val_2222_);
lean_dec_ref_known(v___x_2220_, 1);
return v_val_2222_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit___redArg(lean_object* v_v_2223_){
_start:
{
lean_object* v_kind_2224_; 
v_kind_2224_ = lean_ctor_get(v_v_2223_, 0);
if (lean_obj_tag(v_kind_2224_) == 6)
{
lean_object* v_a_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2225_ = lean_ctor_get(v_kind_2224_, 0);
v___x_2226_ = 1;
v___x_2227_ = lean_int_neg(v_a_2225_);
v___x_2228_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2227_);
v___x_2229_ = lp_kanon_Kanon_whenSome___redArg(v___x_2226_, v___x_2228_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_box(0);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit___redArg___boxed(lean_object* v_v_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = lp_kanon__tiny__values_Tiny_neg_r__lit___redArg(v_v_2231_);
lean_dec_ref(v_v_2231_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit(lean_object* v_O_2233_, lean_object* v_v_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = lp_kanon__tiny__values_Tiny_neg_r__lit___redArg(v_v_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__lit___boxed(lean_object* v_O_2236_, lean_object* v_v_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = lp_kanon__tiny__values_Tiny_neg_r__lit(v_O_2236_, v_v_2237_);
lean_dec_ref(v_v_2237_);
lean_dec_ref(v_O_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_r__default(lean_object* v_O_2239_, lean_object* v_v_2240_){
_start:
{
lean_object* v_sub_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_sub_2241_ = lean_ctor_get(v_O_2239_, 9);
lean_inc_ref(v_sub_2241_);
lean_dec_ref(v_O_2239_);
v___x_2242_ = 1;
v___x_2243_ = lp_kanon__tiny__values_Tiny_zero;
v___x_2244_ = lean_apply_2(v_sub_2241_, v___x_2243_, v_v_2240_);
v___x_2245_ = lp_kanon_Kanon_whenSome___redArg(v___x_2242_, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_neg_step(lean_object* v_O_2246_, lean_object* v_v_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2248_ = lp_kanon__tiny__values_Tiny_neg_r__lit___redArg(v_v_2247_);
lean_inc_ref(v_v_2247_);
v___x_2249_ = lp_kanon__tiny__values_Tiny_neg_r__default(v_O_2246_, v_v_2247_);
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2248_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lp_kanon_Kanon_firstSome___redArg(v___x_2252_);
lean_dec_ref_known(v___x_2252_, 2);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = lp_kanon__tiny__values_Tiny_neg_spec(v_v_2247_);
return v___x_2254_;
}
else
{
lean_object* v_val_2255_; 
lean_dec_ref(v_v_2247_);
v_val_2255_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v___x_2253_, 1);
return v_val_2255_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits___redArg(lean_object* v_v1_2256_, lean_object* v_v2_2257_){
_start:
{
lean_object* v_kind_2258_; 
v_kind_2258_ = lean_ctor_get(v_v1_2256_, 0);
if (lean_obj_tag(v_kind_2258_) == 6)
{
lean_object* v_kind_2259_; 
v_kind_2259_ = lean_ctor_get(v_v2_2257_, 0);
if (lean_obj_tag(v_kind_2259_) == 6)
{
lean_object* v_a_2260_; lean_object* v_a_2261_; uint8_t v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2260_ = lean_ctor_get(v_kind_2258_, 0);
v_a_2261_ = lean_ctor_get(v_kind_2259_, 0);
v___x_2262_ = 1;
v___x_2263_ = lean_int_dec_lt(v_a_2260_, v_a_2261_);
v___x_2264_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_2263_);
v___x_2265_ = lp_kanon_Kanon_whenSome___redArg(v___x_2262_, v___x_2264_);
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_box(0);
return v___x_2266_;
}
}
else
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_box(0);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits___redArg___boxed(lean_object* v_v1_2268_, lean_object* v_v2_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = lp_kanon__tiny__values_Tiny_lt_r__lits___redArg(v_v1_2268_, v_v2_2269_);
lean_dec_ref(v_v2_2269_);
lean_dec_ref(v_v1_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits(lean_object* v_O_2271_, lean_object* v_v1_2272_, lean_object* v_v2_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = lp_kanon__tiny__values_Tiny_lt_r__lits___redArg(v_v1_2272_, v_v2_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__lits___boxed(lean_object* v_O_2275_, lean_object* v_v1_2276_, lean_object* v_v2_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = lp_kanon__tiny__values_Tiny_lt_r__lits(v_O_2275_, v_v1_2276_, v_v2_2277_);
lean_dec_ref(v_v2_2277_);
lean_dec_ref(v_v1_2276_);
lean_dec_ref(v_O_2275_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__add__const(lean_object* v_O_2279_, lean_object* v_v1_2280_, lean_object* v_v2_2281_){
_start:
{
lean_object* v_kind_2282_; lean_object* v___y_2284_; 
v_kind_2282_ = lean_ctor_get(v_v1_2280_, 0);
lean_inc_ref(v_kind_2282_);
lean_dec_ref(v_v1_2280_);
if (lean_obj_tag(v_kind_2282_) == 2)
{
uint8_t v_a_2298_; 
v_a_2298_ = lean_ctor_get_uint8(v_kind_2282_, sizeof(void*)*2);
if (v_a_2298_ == 5)
{
lean_object* v_a_2299_; lean_object* v_kind_2300_; 
v_a_2299_ = lean_ctor_get(v_kind_2282_, 1);
v_kind_2300_ = lean_ctor_get(v_a_2299_, 0);
if (lean_obj_tag(v_kind_2300_) == 6)
{
lean_object* v_kind_2301_; 
v_kind_2301_ = lean_ctor_get(v_v2_2281_, 0);
if (lean_obj_tag(v_kind_2301_) == 6)
{
lean_object* v_a_2302_; lean_object* v_a_2303_; lean_object* v_a_2304_; lean_object* v_lt_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2302_ = lean_ctor_get(v_kind_2282_, 0);
v_a_2303_ = lean_ctor_get(v_kind_2300_, 0);
v_a_2304_ = lean_ctor_get(v_kind_2301_, 0);
v_lt_2305_ = lean_ctor_get(v_O_2279_, 15);
v___x_2306_ = 1;
v___x_2307_ = lean_int_sub(v_a_2304_, v_a_2303_);
v___x_2308_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2307_);
lean_inc_ref(v_lt_2305_);
lean_inc_ref(v_a_2302_);
v___x_2309_ = lean_apply_2(v_lt_2305_, v_a_2302_, v___x_2308_);
v___x_2310_ = lp_kanon_Kanon_whenSome___redArg(v___x_2306_, v___x_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
v___y_2284_ = v___x_2310_;
goto v___jp_2283_;
}
else
{
lean_dec_ref_known(v_kind_2282_, 2);
lean_dec_ref(v_O_2279_);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_box(0);
v___y_2284_ = v___x_2311_;
goto v___jp_2283_;
}
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_box(0);
v___y_2284_ = v___x_2312_;
goto v___jp_2283_;
}
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_box(0);
v___y_2284_ = v___x_2313_;
goto v___jp_2283_;
}
}
else
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_box(0);
v___y_2284_ = v___x_2314_;
goto v___jp_2283_;
}
v___jp_2283_:
{
if (lean_obj_tag(v_kind_2282_) == 2)
{
uint8_t v_a_2285_; 
v_a_2285_ = lean_ctor_get_uint8(v_kind_2282_, sizeof(void*)*2);
if (v_a_2285_ == 5)
{
lean_object* v_a_2286_; lean_object* v_kind_2287_; 
v_a_2286_ = lean_ctor_get(v_kind_2282_, 0);
v_kind_2287_ = lean_ctor_get(v_a_2286_, 0);
lean_inc_ref(v_kind_2287_);
if (lean_obj_tag(v_kind_2287_) == 6)
{
lean_object* v_kind_2288_; 
v_kind_2288_ = lean_ctor_get(v_v2_2281_, 0);
if (lean_obj_tag(v_kind_2288_) == 6)
{
lean_object* v_a_2289_; lean_object* v_a_2290_; lean_object* v_a_2291_; lean_object* v_lt_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec(v___y_2284_);
v_a_2289_ = lean_ctor_get(v_kind_2282_, 1);
lean_inc_ref(v_a_2289_);
lean_dec_ref_known(v_kind_2282_, 2);
v_a_2290_ = lean_ctor_get(v_kind_2287_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v_kind_2287_, 1);
v_a_2291_ = lean_ctor_get(v_kind_2288_, 0);
v_lt_2292_ = lean_ctor_get(v_O_2279_, 15);
lean_inc_ref(v_lt_2292_);
lean_dec_ref(v_O_2279_);
v___x_2293_ = 1;
v___x_2294_ = lean_int_sub(v_a_2291_, v_a_2290_);
lean_dec(v_a_2290_);
v___x_2295_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2294_);
v___x_2296_ = lean_apply_2(v_lt_2292_, v_a_2289_, v___x_2295_);
v___x_2297_ = lp_kanon_Kanon_whenSome___redArg(v___x_2293_, v___x_2296_);
return v___x_2297_;
}
else
{
lean_dec_ref_known(v_kind_2287_, 1);
lean_dec_ref_known(v_kind_2282_, 2);
lean_dec_ref(v_O_2279_);
return v___y_2284_;
}
}
else
{
lean_dec_ref(v_kind_2287_);
lean_dec_ref_known(v_kind_2282_, 2);
lean_dec_ref(v_O_2279_);
return v___y_2284_;
}
}
else
{
lean_dec_ref_known(v_kind_2282_, 2);
lean_dec_ref(v_O_2279_);
return v___y_2284_;
}
}
else
{
lean_dec_ref(v_kind_2282_);
lean_dec_ref(v_O_2279_);
return v___y_2284_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__add__const___boxed(lean_object* v_O_2315_, lean_object* v_v1_2316_, lean_object* v_v2_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = lp_kanon__tiny__values_Tiny_lt_r__add__const(v_O_2315_, v_v1_2316_, v_v2_2317_);
lean_dec_ref(v_v2_2317_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__add(lean_object* v_O_2319_, lean_object* v_v1_2320_, lean_object* v_v2_2321_){
_start:
{
lean_object* v_kind_2322_; lean_object* v___y_2324_; 
v_kind_2322_ = lean_ctor_get(v_v1_2320_, 0);
if (lean_obj_tag(v_kind_2322_) == 6)
{
lean_object* v_kind_2338_; 
v_kind_2338_ = lean_ctor_get(v_v2_2321_, 0);
if (lean_obj_tag(v_kind_2338_) == 2)
{
uint8_t v_a_2339_; 
v_a_2339_ = lean_ctor_get_uint8(v_kind_2338_, sizeof(void*)*2);
if (v_a_2339_ == 5)
{
lean_object* v_a_2340_; lean_object* v_kind_2341_; 
v_a_2340_ = lean_ctor_get(v_kind_2338_, 1);
v_kind_2341_ = lean_ctor_get(v_a_2340_, 0);
if (lean_obj_tag(v_kind_2341_) == 6)
{
lean_object* v_a_2342_; lean_object* v_a_2343_; lean_object* v_a_2344_; lean_object* v_lt_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2342_ = lean_ctor_get(v_kind_2322_, 0);
v_a_2343_ = lean_ctor_get(v_kind_2338_, 0);
v_a_2344_ = lean_ctor_get(v_kind_2341_, 0);
v_lt_2345_ = lean_ctor_get(v_O_2319_, 15);
v___x_2346_ = 1;
v___x_2347_ = lean_int_sub(v_a_2342_, v_a_2344_);
v___x_2348_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2347_);
lean_inc_ref(v_lt_2345_);
lean_inc_ref(v_a_2343_);
v___x_2349_ = lean_apply_2(v_lt_2345_, v___x_2348_, v_a_2343_);
v___x_2350_ = lp_kanon_Kanon_whenSome___redArg(v___x_2346_, v___x_2349_);
if (lean_obj_tag(v___x_2350_) == 0)
{
v___y_2324_ = v___x_2350_;
goto v___jp_2323_;
}
else
{
lean_dec_ref(v_v2_2321_);
lean_dec_ref(v_O_2319_);
return v___x_2350_;
}
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_box(0);
v___y_2324_ = v___x_2351_;
goto v___jp_2323_;
}
}
else
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_box(0);
v___y_2324_ = v___x_2352_;
goto v___jp_2323_;
}
}
else
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_box(0);
v___y_2324_ = v___x_2353_;
goto v___jp_2323_;
}
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_box(0);
v___y_2324_ = v___x_2354_;
goto v___jp_2323_;
}
v___jp_2323_:
{
if (lean_obj_tag(v_kind_2322_) == 6)
{
lean_object* v_kind_2325_; 
v_kind_2325_ = lean_ctor_get(v_v2_2321_, 0);
lean_inc_ref(v_kind_2325_);
lean_dec_ref(v_v2_2321_);
if (lean_obj_tag(v_kind_2325_) == 2)
{
uint8_t v_a_2326_; 
v_a_2326_ = lean_ctor_get_uint8(v_kind_2325_, sizeof(void*)*2);
if (v_a_2326_ == 5)
{
lean_object* v_a_2327_; lean_object* v_kind_2328_; 
v_a_2327_ = lean_ctor_get(v_kind_2325_, 0);
v_kind_2328_ = lean_ctor_get(v_a_2327_, 0);
lean_inc_ref(v_kind_2328_);
if (lean_obj_tag(v_kind_2328_) == 6)
{
lean_object* v_a_2329_; lean_object* v_a_2330_; lean_object* v_a_2331_; lean_object* v_lt_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v___y_2324_);
v_a_2329_ = lean_ctor_get(v_kind_2322_, 0);
v_a_2330_ = lean_ctor_get(v_kind_2325_, 1);
lean_inc_ref(v_a_2330_);
lean_dec_ref_known(v_kind_2325_, 2);
v_a_2331_ = lean_ctor_get(v_kind_2328_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v_kind_2328_, 1);
v_lt_2332_ = lean_ctor_get(v_O_2319_, 15);
lean_inc_ref(v_lt_2332_);
lean_dec_ref(v_O_2319_);
v___x_2333_ = 1;
v___x_2334_ = lean_int_sub(v_a_2329_, v_a_2331_);
lean_dec(v_a_2331_);
v___x_2335_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2334_);
v___x_2336_ = lean_apply_2(v_lt_2332_, v___x_2335_, v_a_2330_);
v___x_2337_ = lp_kanon_Kanon_whenSome___redArg(v___x_2333_, v___x_2336_);
return v___x_2337_;
}
else
{
lean_dec_ref(v_kind_2328_);
lean_dec_ref_known(v_kind_2325_, 2);
lean_dec_ref(v_O_2319_);
return v___y_2324_;
}
}
else
{
lean_dec_ref_known(v_kind_2325_, 2);
lean_dec_ref(v_O_2319_);
return v___y_2324_;
}
}
else
{
lean_dec_ref(v_kind_2325_);
lean_dec_ref(v_O_2319_);
return v___y_2324_;
}
}
else
{
lean_dec_ref(v_v2_2321_);
lean_dec_ref(v_O_2319_);
return v___y_2324_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__add___boxed(lean_object* v_O_2355_, lean_object* v_v1_2356_, lean_object* v_v2_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = lp_kanon__tiny__values_Tiny_lt_r__const__add(v_O_2355_, v_v1_2356_, v_v2_2357_);
lean_dec_ref(v_v1_2356_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__sub__const(lean_object* v_O_2359_, lean_object* v_v1_2360_, lean_object* v_v2_2361_){
_start:
{
lean_object* v_kind_2362_; 
v_kind_2362_ = lean_ctor_get(v_v1_2360_, 0);
lean_inc_ref(v_kind_2362_);
lean_dec_ref(v_v1_2360_);
if (lean_obj_tag(v_kind_2362_) == 2)
{
uint8_t v_a_2363_; 
v_a_2363_ = lean_ctor_get_uint8(v_kind_2362_, sizeof(void*)*2);
if (v_a_2363_ == 6)
{
lean_object* v_a_2364_; lean_object* v_kind_2365_; 
v_a_2364_ = lean_ctor_get(v_kind_2362_, 1);
v_kind_2365_ = lean_ctor_get(v_a_2364_, 0);
lean_inc_ref(v_kind_2365_);
if (lean_obj_tag(v_kind_2365_) == 6)
{
lean_object* v_kind_2366_; 
v_kind_2366_ = lean_ctor_get(v_v2_2361_, 0);
if (lean_obj_tag(v_kind_2366_) == 6)
{
lean_object* v_a_2367_; lean_object* v_a_2368_; lean_object* v_a_2369_; lean_object* v_lt_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_a_2367_ = lean_ctor_get(v_kind_2362_, 0);
lean_inc_ref(v_a_2367_);
lean_dec_ref_known(v_kind_2362_, 2);
v_a_2368_ = lean_ctor_get(v_kind_2365_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v_kind_2365_, 1);
v_a_2369_ = lean_ctor_get(v_kind_2366_, 0);
v_lt_2370_ = lean_ctor_get(v_O_2359_, 15);
lean_inc_ref(v_lt_2370_);
lean_dec_ref(v_O_2359_);
v___x_2371_ = 1;
v___x_2372_ = lean_int_add(v_a_2369_, v_a_2368_);
lean_dec(v_a_2368_);
v___x_2373_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2372_);
v___x_2374_ = lean_apply_2(v_lt_2370_, v_a_2367_, v___x_2373_);
v___x_2375_ = lp_kanon_Kanon_whenSome___redArg(v___x_2371_, v___x_2374_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
lean_dec_ref_known(v_kind_2365_, 1);
lean_dec_ref_known(v_kind_2362_, 2);
lean_dec_ref(v_O_2359_);
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
}
else
{
lean_object* v___x_2377_; 
lean_dec_ref(v_kind_2365_);
lean_dec_ref_known(v_kind_2362_, 2);
lean_dec_ref(v_O_2359_);
v___x_2377_ = lean_box(0);
return v___x_2377_;
}
}
else
{
lean_object* v___x_2378_; 
lean_dec_ref_known(v_kind_2362_, 2);
lean_dec_ref(v_O_2359_);
v___x_2378_ = lean_box(0);
return v___x_2378_;
}
}
else
{
lean_object* v___x_2379_; 
lean_dec_ref(v_kind_2362_);
lean_dec_ref(v_O_2359_);
v___x_2379_ = lean_box(0);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__sub__const___boxed(lean_object* v_O_2380_, lean_object* v_v1_2381_, lean_object* v_v2_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = lp_kanon__tiny__values_Tiny_lt_r__sub__const(v_O_2380_, v_v1_2381_, v_v2_2382_);
lean_dec_ref(v_v2_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__rsub__const(lean_object* v_O_2384_, lean_object* v_v1_2385_, lean_object* v_v2_2386_){
_start:
{
lean_object* v_kind_2387_; 
v_kind_2387_ = lean_ctor_get(v_v1_2385_, 0);
lean_inc_ref(v_kind_2387_);
lean_dec_ref(v_v1_2385_);
if (lean_obj_tag(v_kind_2387_) == 2)
{
uint8_t v_a_2388_; 
v_a_2388_ = lean_ctor_get_uint8(v_kind_2387_, sizeof(void*)*2);
if (v_a_2388_ == 6)
{
lean_object* v_a_2389_; lean_object* v_kind_2390_; 
v_a_2389_ = lean_ctor_get(v_kind_2387_, 0);
v_kind_2390_ = lean_ctor_get(v_a_2389_, 0);
lean_inc_ref(v_kind_2390_);
if (lean_obj_tag(v_kind_2390_) == 6)
{
lean_object* v_kind_2391_; 
v_kind_2391_ = lean_ctor_get(v_v2_2386_, 0);
if (lean_obj_tag(v_kind_2391_) == 6)
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v_a_2394_; lean_object* v_lt_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_a_2392_ = lean_ctor_get(v_kind_2387_, 1);
lean_inc_ref(v_a_2392_);
lean_dec_ref_known(v_kind_2387_, 2);
v_a_2393_ = lean_ctor_get(v_kind_2390_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v_kind_2390_, 1);
v_a_2394_ = lean_ctor_get(v_kind_2391_, 0);
v_lt_2395_ = lean_ctor_get(v_O_2384_, 15);
lean_inc_ref(v_lt_2395_);
lean_dec_ref(v_O_2384_);
v___x_2396_ = 1;
v___x_2397_ = lean_int_sub(v_a_2393_, v_a_2394_);
lean_dec(v_a_2393_);
v___x_2398_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2397_);
v___x_2399_ = lean_apply_2(v_lt_2395_, v___x_2398_, v_a_2392_);
v___x_2400_ = lp_kanon_Kanon_whenSome___redArg(v___x_2396_, v___x_2399_);
return v___x_2400_;
}
else
{
lean_object* v___x_2401_; 
lean_dec_ref_known(v_kind_2390_, 1);
lean_dec_ref_known(v_kind_2387_, 2);
lean_dec_ref(v_O_2384_);
v___x_2401_ = lean_box(0);
return v___x_2401_;
}
}
else
{
lean_object* v___x_2402_; 
lean_dec_ref(v_kind_2390_);
lean_dec_ref_known(v_kind_2387_, 2);
lean_dec_ref(v_O_2384_);
v___x_2402_ = lean_box(0);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2403_; 
lean_dec_ref_known(v_kind_2387_, 2);
lean_dec_ref(v_O_2384_);
v___x_2403_ = lean_box(0);
return v___x_2403_;
}
}
else
{
lean_object* v___x_2404_; 
lean_dec_ref(v_kind_2387_);
lean_dec_ref(v_O_2384_);
v___x_2404_ = lean_box(0);
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__rsub__const___boxed(lean_object* v_O_2405_, lean_object* v_v1_2406_, lean_object* v_v2_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = lp_kanon__tiny__values_Tiny_lt_r__rsub__const(v_O_2405_, v_v1_2406_, v_v2_2407_);
lean_dec_ref(v_v2_2407_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__sub(lean_object* v_O_2409_, lean_object* v_v1_2410_, lean_object* v_v2_2411_){
_start:
{
lean_object* v_kind_2412_; 
v_kind_2412_ = lean_ctor_get(v_v1_2410_, 0);
if (lean_obj_tag(v_kind_2412_) == 6)
{
lean_object* v_kind_2413_; 
v_kind_2413_ = lean_ctor_get(v_v2_2411_, 0);
lean_inc_ref(v_kind_2413_);
lean_dec_ref(v_v2_2411_);
if (lean_obj_tag(v_kind_2413_) == 2)
{
uint8_t v_a_2414_; 
v_a_2414_ = lean_ctor_get_uint8(v_kind_2413_, sizeof(void*)*2);
if (v_a_2414_ == 6)
{
lean_object* v_a_2415_; lean_object* v_kind_2416_; 
v_a_2415_ = lean_ctor_get(v_kind_2413_, 1);
v_kind_2416_ = lean_ctor_get(v_a_2415_, 0);
lean_inc_ref(v_kind_2416_);
if (lean_obj_tag(v_kind_2416_) == 6)
{
lean_object* v_a_2417_; lean_object* v_a_2418_; lean_object* v_a_2419_; lean_object* v_lt_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2417_ = lean_ctor_get(v_kind_2412_, 0);
v_a_2418_ = lean_ctor_get(v_kind_2413_, 0);
lean_inc_ref(v_a_2418_);
lean_dec_ref_known(v_kind_2413_, 2);
v_a_2419_ = lean_ctor_get(v_kind_2416_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v_kind_2416_, 1);
v_lt_2420_ = lean_ctor_get(v_O_2409_, 15);
lean_inc_ref(v_lt_2420_);
lean_dec_ref(v_O_2409_);
v___x_2421_ = 1;
v___x_2422_ = lean_int_add(v_a_2417_, v_a_2419_);
lean_dec(v_a_2419_);
v___x_2423_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2422_);
v___x_2424_ = lean_apply_2(v_lt_2420_, v___x_2423_, v_a_2418_);
v___x_2425_ = lp_kanon_Kanon_whenSome___redArg(v___x_2421_, v___x_2424_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; 
lean_dec_ref(v_kind_2416_);
lean_dec_ref_known(v_kind_2413_, 2);
lean_dec_ref(v_O_2409_);
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
}
else
{
lean_object* v___x_2427_; 
lean_dec_ref_known(v_kind_2413_, 2);
lean_dec_ref(v_O_2409_);
v___x_2427_ = lean_box(0);
return v___x_2427_;
}
}
else
{
lean_object* v___x_2428_; 
lean_dec_ref(v_kind_2413_);
lean_dec_ref(v_O_2409_);
v___x_2428_ = lean_box(0);
return v___x_2428_;
}
}
else
{
lean_object* v___x_2429_; 
lean_dec_ref(v_v2_2411_);
lean_dec_ref(v_O_2409_);
v___x_2429_ = lean_box(0);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__sub___boxed(lean_object* v_O_2430_, lean_object* v_v1_2431_, lean_object* v_v2_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = lp_kanon__tiny__values_Tiny_lt_r__const__sub(v_O_2430_, v_v1_2431_, v_v2_2432_);
lean_dec_ref(v_v1_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__rsub(lean_object* v_O_2434_, lean_object* v_v1_2435_, lean_object* v_v2_2436_){
_start:
{
lean_object* v_kind_2437_; 
v_kind_2437_ = lean_ctor_get(v_v1_2435_, 0);
if (lean_obj_tag(v_kind_2437_) == 6)
{
lean_object* v_kind_2438_; 
v_kind_2438_ = lean_ctor_get(v_v2_2436_, 0);
lean_inc_ref(v_kind_2438_);
lean_dec_ref(v_v2_2436_);
if (lean_obj_tag(v_kind_2438_) == 2)
{
uint8_t v_a_2439_; 
v_a_2439_ = lean_ctor_get_uint8(v_kind_2438_, sizeof(void*)*2);
if (v_a_2439_ == 6)
{
lean_object* v_a_2440_; lean_object* v_kind_2441_; 
v_a_2440_ = lean_ctor_get(v_kind_2438_, 0);
v_kind_2441_ = lean_ctor_get(v_a_2440_, 0);
lean_inc_ref(v_kind_2441_);
if (lean_obj_tag(v_kind_2441_) == 6)
{
lean_object* v_a_2442_; lean_object* v_a_2443_; lean_object* v_a_2444_; lean_object* v_lt_2445_; uint8_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_a_2442_ = lean_ctor_get(v_kind_2437_, 0);
v_a_2443_ = lean_ctor_get(v_kind_2438_, 1);
lean_inc_ref(v_a_2443_);
lean_dec_ref_known(v_kind_2438_, 2);
v_a_2444_ = lean_ctor_get(v_kind_2441_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v_kind_2441_, 1);
v_lt_2445_ = lean_ctor_get(v_O_2434_, 15);
lean_inc_ref(v_lt_2445_);
lean_dec_ref(v_O_2434_);
v___x_2446_ = 1;
v___x_2447_ = lean_int_sub(v_a_2444_, v_a_2442_);
lean_dec(v_a_2444_);
v___x_2448_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2447_);
v___x_2449_ = lean_apply_2(v_lt_2445_, v_a_2443_, v___x_2448_);
v___x_2450_ = lp_kanon_Kanon_whenSome___redArg(v___x_2446_, v___x_2449_);
return v___x_2450_;
}
else
{
lean_object* v___x_2451_; 
lean_dec_ref(v_kind_2441_);
lean_dec_ref_known(v_kind_2438_, 2);
lean_dec_ref(v_O_2434_);
v___x_2451_ = lean_box(0);
return v___x_2451_;
}
}
else
{
lean_object* v___x_2452_; 
lean_dec_ref_known(v_kind_2438_, 2);
lean_dec_ref(v_O_2434_);
v___x_2452_ = lean_box(0);
return v___x_2452_;
}
}
else
{
lean_object* v___x_2453_; 
lean_dec_ref(v_kind_2438_);
lean_dec_ref(v_O_2434_);
v___x_2453_ = lean_box(0);
return v___x_2453_;
}
}
else
{
lean_object* v___x_2454_; 
lean_dec_ref(v_v2_2436_);
lean_dec_ref(v_O_2434_);
v___x_2454_ = lean_box(0);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__rsub___boxed(lean_object* v_O_2455_, lean_object* v_v1_2456_, lean_object* v_v2_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = lp_kanon__tiny__values_Tiny_lt_r__const__rsub(v_O_2455_, v_v1_2456_, v_v2_2457_);
lean_dec_ref(v_v1_2456_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mul(lean_object* v_O_2459_, lean_object* v_v1_2460_, lean_object* v_v2_2461_){
_start:
{
lean_object* v___y_2463_; uint8_t v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v_kind_2479_; lean_object* v___y_2481_; lean_object* v___y_2509_; 
v_kind_2479_ = lean_ctor_get(v_v1_2460_, 0);
if (lean_obj_tag(v_kind_2479_) == 6)
{
lean_object* v_kind_2510_; 
v_kind_2510_ = lean_ctor_get(v_v2_2461_, 0);
if (lean_obj_tag(v_kind_2510_) == 2)
{
uint8_t v_a_2511_; 
v_a_2511_ = lean_ctor_get_uint8(v_kind_2510_, sizeof(void*)*2);
if (v_a_2511_ == 7)
{
lean_object* v_a_2512_; lean_object* v_kind_2513_; 
v_a_2512_ = lean_ctor_get(v_kind_2510_, 0);
v_kind_2513_ = lean_ctor_get(v_a_2512_, 0);
if (lean_obj_tag(v_kind_2513_) == 6)
{
lean_object* v_a_2514_; lean_object* v_a_2515_; lean_object* v_a_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2531_; 
v_a_2514_ = lean_ctor_get(v_kind_2479_, 0);
v_a_2515_ = lean_ctor_get(v_kind_2510_, 1);
v_a_2516_ = lean_ctor_get(v_kind_2513_, 0);
v___x_2517_ = 1;
v___x_2518_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_2531_ = lean_int_dec_eq(v_a_2516_, v___x_2518_);
if (v___x_2531_ == 0)
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Int_decidableDvd(v_a_2516_, v_a_2514_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_int_dec_lt(v___x_2518_, v_a_2514_);
if (v___x_2533_ == 0)
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_int_dec_lt(v___x_2518_, v_a_2516_);
if (v___x_2534_ == 0)
{
lean_object* v_leq_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_leq_2535_ = lean_ctor_get(v_O_2459_, 16);
v___x_2536_ = lean_int_div(v_a_2514_, v_a_2516_);
v___x_2537_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2536_);
lean_inc_ref(v_leq_2535_);
lean_inc_ref(v_a_2515_);
v___x_2538_ = lean_apply_2(v_leq_2535_, v_a_2515_, v___x_2537_);
v___x_2539_ = lp_kanon_Kanon_whenSome___redArg(v___x_2517_, v___x_2538_);
v___y_2509_ = v___x_2539_;
goto v___jp_2508_;
}
else
{
lean_object* v_leq_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_leq_2540_ = lean_ctor_get(v_O_2459_, 16);
v___x_2541_ = lean_int_div(v_a_2514_, v_a_2516_);
v___x_2542_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2541_);
lean_inc_ref(v_leq_2540_);
lean_inc_ref(v_a_2515_);
v___x_2543_ = lean_apply_2(v_leq_2540_, v___x_2542_, v_a_2515_);
v___x_2544_ = lp_kanon_Kanon_whenSome___redArg(v___x_2517_, v___x_2543_);
v___y_2509_ = v___x_2544_;
goto v___jp_2508_;
}
}
else
{
goto v___jp_2519_;
}
}
else
{
goto v___jp_2519_;
}
}
else
{
uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_int_dec_lt(v_a_2514_, v___x_2518_);
v___x_2546_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_2545_);
v___x_2547_ = lp_kanon_Kanon_whenSome___redArg(v___x_2517_, v___x_2546_);
v___y_2509_ = v___x_2547_;
goto v___jp_2508_;
}
v___jp_2519_:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_int_dec_lt(v___x_2518_, v_a_2516_);
if (v___x_2520_ == 0)
{
lean_object* v_lt_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_lt_2521_ = lean_ctor_get(v_O_2459_, 15);
v___x_2522_ = lean_int_div(v_a_2514_, v_a_2516_);
v___x_2523_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2522_);
lean_inc_ref(v_lt_2521_);
lean_inc_ref(v_a_2515_);
v___x_2524_ = lean_apply_2(v_lt_2521_, v_a_2515_, v___x_2523_);
v___x_2525_ = lp_kanon_Kanon_whenSome___redArg(v___x_2517_, v___x_2524_);
v___y_2509_ = v___x_2525_;
goto v___jp_2508_;
}
else
{
lean_object* v_lt_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_lt_2526_ = lean_ctor_get(v_O_2459_, 15);
v___x_2527_ = lean_int_div(v_a_2514_, v_a_2516_);
v___x_2528_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2527_);
lean_inc_ref(v_lt_2526_);
lean_inc_ref(v_a_2515_);
v___x_2529_ = lean_apply_2(v_lt_2526_, v___x_2528_, v_a_2515_);
v___x_2530_ = lp_kanon_Kanon_whenSome___redArg(v___x_2517_, v___x_2529_);
v___y_2509_ = v___x_2530_;
goto v___jp_2508_;
}
}
}
else
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_box(0);
v___y_2481_ = v___x_2548_;
goto v___jp_2480_;
}
}
else
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_box(0);
v___y_2481_ = v___x_2549_;
goto v___jp_2480_;
}
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_box(0);
v___y_2481_ = v___x_2550_;
goto v___jp_2480_;
}
}
else
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_box(0);
v___y_2481_ = v___x_2551_;
goto v___jp_2480_;
}
v___jp_2462_:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_int_dec_lt(v___y_2467_, v___y_2466_);
if (v___x_2468_ == 0)
{
lean_object* v_lt_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_lt_2469_ = lean_ctor_get(v_O_2459_, 15);
lean_inc_ref(v_lt_2469_);
lean_dec_ref(v_O_2459_);
v___x_2470_ = lean_int_div(v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
v___x_2471_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2470_);
v___x_2472_ = lean_apply_2(v_lt_2469_, v___y_2463_, v___x_2471_);
v___x_2473_ = lp_kanon_Kanon_whenSome___redArg(v___y_2464_, v___x_2472_);
return v___x_2473_;
}
else
{
lean_object* v_lt_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_lt_2474_ = lean_ctor_get(v_O_2459_, 15);
lean_inc_ref(v_lt_2474_);
lean_dec_ref(v_O_2459_);
v___x_2475_ = lean_int_div(v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
v___x_2476_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2475_);
v___x_2477_ = lean_apply_2(v_lt_2474_, v___x_2476_, v___y_2463_);
v___x_2478_ = lp_kanon_Kanon_whenSome___redArg(v___y_2464_, v___x_2477_);
return v___x_2478_;
}
}
v___jp_2480_:
{
if (lean_obj_tag(v_kind_2479_) == 6)
{
lean_object* v_kind_2482_; 
v_kind_2482_ = lean_ctor_get(v_v2_2461_, 0);
lean_inc_ref(v_kind_2482_);
lean_dec_ref(v_v2_2461_);
if (lean_obj_tag(v_kind_2482_) == 2)
{
uint8_t v_a_2483_; 
v_a_2483_ = lean_ctor_get_uint8(v_kind_2482_, sizeof(void*)*2);
if (v_a_2483_ == 7)
{
lean_object* v_a_2484_; lean_object* v_kind_2485_; 
v_a_2484_ = lean_ctor_get(v_kind_2482_, 1);
v_kind_2485_ = lean_ctor_get(v_a_2484_, 0);
lean_inc_ref(v_kind_2485_);
if (lean_obj_tag(v_kind_2485_) == 6)
{
lean_object* v_a_2486_; lean_object* v_a_2487_; lean_object* v_a_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
lean_dec(v___y_2481_);
v_a_2486_ = lean_ctor_get(v_kind_2479_, 0);
v_a_2487_ = lean_ctor_get(v_kind_2482_, 0);
lean_inc_ref(v_a_2487_);
lean_dec_ref_known(v_kind_2482_, 2);
v_a_2488_ = lean_ctor_get(v_kind_2485_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v_kind_2485_, 1);
v___x_2489_ = 1;
v___x_2490_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_2491_ = lean_int_dec_eq(v_a_2488_, v___x_2490_);
if (v___x_2491_ == 0)
{
uint8_t v___x_2492_; 
v___x_2492_ = l_Int_decidableDvd(v_a_2488_, v_a_2486_);
if (v___x_2492_ == 0)
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_int_dec_lt(v___x_2490_, v_a_2486_);
if (v___x_2493_ == 0)
{
uint8_t v___x_2494_; 
v___x_2494_ = lean_int_dec_lt(v___x_2490_, v_a_2488_);
if (v___x_2494_ == 0)
{
lean_object* v_leq_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_leq_2495_ = lean_ctor_get(v_O_2459_, 16);
lean_inc_ref(v_leq_2495_);
lean_dec_ref(v_O_2459_);
v___x_2496_ = lean_int_div(v_a_2486_, v_a_2488_);
lean_dec(v_a_2488_);
v___x_2497_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2496_);
v___x_2498_ = lean_apply_2(v_leq_2495_, v_a_2487_, v___x_2497_);
v___x_2499_ = lp_kanon_Kanon_whenSome___redArg(v___x_2489_, v___x_2498_);
return v___x_2499_;
}
else
{
lean_object* v_leq_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_leq_2500_ = lean_ctor_get(v_O_2459_, 16);
lean_inc_ref(v_leq_2500_);
lean_dec_ref(v_O_2459_);
v___x_2501_ = lean_int_div(v_a_2486_, v_a_2488_);
lean_dec(v_a_2488_);
v___x_2502_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2501_);
v___x_2503_ = lean_apply_2(v_leq_2500_, v___x_2502_, v_a_2487_);
v___x_2504_ = lp_kanon_Kanon_whenSome___redArg(v___x_2489_, v___x_2503_);
return v___x_2504_;
}
}
else
{
v___y_2463_ = v_a_2487_;
v___y_2464_ = v___x_2489_;
v___y_2465_ = v_a_2486_;
v___y_2466_ = v_a_2488_;
v___y_2467_ = v___x_2490_;
goto v___jp_2462_;
}
}
else
{
v___y_2463_ = v_a_2487_;
v___y_2464_ = v___x_2489_;
v___y_2465_ = v_a_2486_;
v___y_2466_ = v_a_2488_;
v___y_2467_ = v___x_2490_;
goto v___jp_2462_;
}
}
else
{
uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec_ref(v_O_2459_);
v___x_2505_ = lean_int_dec_lt(v_a_2486_, v___x_2490_);
v___x_2506_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_2505_);
v___x_2507_ = lp_kanon_Kanon_whenSome___redArg(v___x_2489_, v___x_2506_);
return v___x_2507_;
}
}
else
{
lean_dec_ref(v_kind_2485_);
lean_dec_ref_known(v_kind_2482_, 2);
lean_dec_ref(v_O_2459_);
return v___y_2481_;
}
}
else
{
lean_dec_ref_known(v_kind_2482_, 2);
lean_dec_ref(v_O_2459_);
return v___y_2481_;
}
}
else
{
lean_dec_ref(v_kind_2482_);
lean_dec_ref(v_O_2459_);
return v___y_2481_;
}
}
else
{
lean_dec_ref(v_v2_2461_);
lean_dec_ref(v_O_2459_);
return v___y_2481_;
}
}
v___jp_2508_:
{
if (lean_obj_tag(v___y_2509_) == 0)
{
v___y_2481_ = v___y_2509_;
goto v___jp_2480_;
}
else
{
lean_dec_ref(v_v2_2461_);
lean_dec_ref(v_O_2459_);
return v___y_2509_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mul___boxed(lean_object* v_O_2552_, lean_object* v_v1_2553_, lean_object* v_v2_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = lp_kanon__tiny__values_Tiny_lt_r__const__mul(v_O_2552_, v_v1_2553_, v_v2_2554_);
lean_dec_ref(v_v1_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mul__const(lean_object* v_O_2556_, lean_object* v_v1_2557_, lean_object* v_v2_2558_){
_start:
{
lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; lean_object* v_kind_2576_; lean_object* v___y_2578_; lean_object* v___y_2606_; 
v_kind_2576_ = lean_ctor_get(v_v1_2557_, 0);
lean_inc_ref(v_kind_2576_);
lean_dec_ref(v_v1_2557_);
if (lean_obj_tag(v_kind_2576_) == 2)
{
uint8_t v_a_2607_; 
v_a_2607_ = lean_ctor_get_uint8(v_kind_2576_, sizeof(void*)*2);
if (v_a_2607_ == 7)
{
lean_object* v_a_2608_; lean_object* v_kind_2609_; 
v_a_2608_ = lean_ctor_get(v_kind_2576_, 1);
v_kind_2609_ = lean_ctor_get(v_a_2608_, 0);
if (lean_obj_tag(v_kind_2609_) == 6)
{
lean_object* v_kind_2610_; 
v_kind_2610_ = lean_ctor_get(v_v2_2558_, 0);
if (lean_obj_tag(v_kind_2610_) == 6)
{
lean_object* v_a_2611_; lean_object* v_a_2612_; lean_object* v_a_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2628_; 
v_a_2611_ = lean_ctor_get(v_kind_2576_, 0);
v_a_2612_ = lean_ctor_get(v_kind_2609_, 0);
v_a_2613_ = lean_ctor_get(v_kind_2610_, 0);
v___x_2614_ = 1;
v___x_2615_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_2628_ = lean_int_dec_eq(v_a_2612_, v___x_2615_);
if (v___x_2628_ == 0)
{
uint8_t v___x_2629_; 
v___x_2629_ = l_Int_decidableDvd(v_a_2612_, v_a_2613_);
if (v___x_2629_ == 0)
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_int_dec_lt(v_a_2613_, v___x_2615_);
if (v___x_2630_ == 0)
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_int_dec_lt(v___x_2615_, v_a_2612_);
if (v___x_2631_ == 0)
{
lean_object* v_leq_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_leq_2632_ = lean_ctor_get(v_O_2556_, 16);
v___x_2633_ = lean_int_div(v_a_2613_, v_a_2612_);
v___x_2634_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2633_);
lean_inc_ref(v_leq_2632_);
lean_inc_ref(v_a_2611_);
v___x_2635_ = lean_apply_2(v_leq_2632_, v___x_2634_, v_a_2611_);
v___x_2636_ = lp_kanon_Kanon_whenSome___redArg(v___x_2614_, v___x_2635_);
v___y_2606_ = v___x_2636_;
goto v___jp_2605_;
}
else
{
lean_object* v_leq_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_leq_2637_ = lean_ctor_get(v_O_2556_, 16);
v___x_2638_ = lean_int_div(v_a_2613_, v_a_2612_);
v___x_2639_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2638_);
lean_inc_ref(v_leq_2637_);
lean_inc_ref(v_a_2611_);
v___x_2640_ = lean_apply_2(v_leq_2637_, v_a_2611_, v___x_2639_);
v___x_2641_ = lp_kanon_Kanon_whenSome___redArg(v___x_2614_, v___x_2640_);
v___y_2606_ = v___x_2641_;
goto v___jp_2605_;
}
}
else
{
goto v___jp_2616_;
}
}
else
{
goto v___jp_2616_;
}
}
else
{
uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_int_dec_lt(v___x_2615_, v_a_2613_);
v___x_2643_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_2642_);
v___x_2644_ = lp_kanon_Kanon_whenSome___redArg(v___x_2614_, v___x_2643_);
v___y_2606_ = v___x_2644_;
goto v___jp_2605_;
}
v___jp_2616_:
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_int_dec_lt(v___x_2615_, v_a_2612_);
if (v___x_2617_ == 0)
{
lean_object* v_lt_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_lt_2618_ = lean_ctor_get(v_O_2556_, 15);
v___x_2619_ = lean_int_div(v_a_2613_, v_a_2612_);
v___x_2620_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2619_);
lean_inc_ref(v_lt_2618_);
lean_inc_ref(v_a_2611_);
v___x_2621_ = lean_apply_2(v_lt_2618_, v___x_2620_, v_a_2611_);
v___x_2622_ = lp_kanon_Kanon_whenSome___redArg(v___x_2614_, v___x_2621_);
v___y_2606_ = v___x_2622_;
goto v___jp_2605_;
}
else
{
lean_object* v_lt_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_lt_2623_ = lean_ctor_get(v_O_2556_, 15);
v___x_2624_ = lean_int_div(v_a_2613_, v_a_2612_);
v___x_2625_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2624_);
lean_inc_ref(v_lt_2623_);
lean_inc_ref(v_a_2611_);
v___x_2626_ = lean_apply_2(v_lt_2623_, v_a_2611_, v___x_2625_);
v___x_2627_ = lp_kanon_Kanon_whenSome___redArg(v___x_2614_, v___x_2626_);
v___y_2606_ = v___x_2627_;
goto v___jp_2605_;
}
}
}
else
{
lean_object* v___x_2645_; 
v___x_2645_ = lean_box(0);
v___y_2578_ = v___x_2645_;
goto v___jp_2577_;
}
}
else
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_box(0);
v___y_2578_ = v___x_2646_;
goto v___jp_2577_;
}
}
else
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_box(0);
v___y_2578_ = v___x_2647_;
goto v___jp_2577_;
}
}
else
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_box(0);
v___y_2578_ = v___x_2648_;
goto v___jp_2577_;
}
v___jp_2559_:
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_int_dec_lt(v___y_2561_, v___y_2560_);
if (v___x_2565_ == 0)
{
lean_object* v_lt_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_lt_2566_ = lean_ctor_get(v_O_2556_, 15);
lean_inc_ref(v_lt_2566_);
lean_dec_ref(v_O_2556_);
v___x_2567_ = lean_int_div(v___y_2564_, v___y_2560_);
lean_dec(v___y_2560_);
v___x_2568_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2567_);
v___x_2569_ = lean_apply_2(v_lt_2566_, v___x_2568_, v___y_2562_);
v___x_2570_ = lp_kanon_Kanon_whenSome___redArg(v___y_2563_, v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v_lt_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_lt_2571_ = lean_ctor_get(v_O_2556_, 15);
lean_inc_ref(v_lt_2571_);
lean_dec_ref(v_O_2556_);
v___x_2572_ = lean_int_div(v___y_2564_, v___y_2560_);
lean_dec(v___y_2560_);
v___x_2573_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2572_);
v___x_2574_ = lean_apply_2(v_lt_2571_, v___y_2562_, v___x_2573_);
v___x_2575_ = lp_kanon_Kanon_whenSome___redArg(v___y_2563_, v___x_2574_);
return v___x_2575_;
}
}
v___jp_2577_:
{
if (lean_obj_tag(v_kind_2576_) == 2)
{
uint8_t v_a_2579_; 
v_a_2579_ = lean_ctor_get_uint8(v_kind_2576_, sizeof(void*)*2);
if (v_a_2579_ == 7)
{
lean_object* v_a_2580_; lean_object* v_kind_2581_; 
v_a_2580_ = lean_ctor_get(v_kind_2576_, 0);
v_kind_2581_ = lean_ctor_get(v_a_2580_, 0);
lean_inc_ref(v_kind_2581_);
if (lean_obj_tag(v_kind_2581_) == 6)
{
lean_object* v_kind_2582_; 
v_kind_2582_ = lean_ctor_get(v_v2_2558_, 0);
if (lean_obj_tag(v_kind_2582_) == 6)
{
lean_object* v_a_2583_; lean_object* v_a_2584_; lean_object* v_a_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
lean_dec(v___y_2578_);
v_a_2583_ = lean_ctor_get(v_kind_2576_, 1);
lean_inc_ref(v_a_2583_);
lean_dec_ref_known(v_kind_2576_, 2);
v_a_2584_ = lean_ctor_get(v_kind_2581_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v_kind_2581_, 1);
v_a_2585_ = lean_ctor_get(v_kind_2582_, 0);
v___x_2586_ = 1;
v___x_2587_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_2588_ = lean_int_dec_eq(v_a_2584_, v___x_2587_);
if (v___x_2588_ == 0)
{
uint8_t v___x_2589_; 
v___x_2589_ = l_Int_decidableDvd(v_a_2584_, v_a_2585_);
if (v___x_2589_ == 0)
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_int_dec_lt(v_a_2585_, v___x_2587_);
if (v___x_2590_ == 0)
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_int_dec_lt(v___x_2587_, v_a_2584_);
if (v___x_2591_ == 0)
{
lean_object* v_leq_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_leq_2592_ = lean_ctor_get(v_O_2556_, 16);
lean_inc_ref(v_leq_2592_);
lean_dec_ref(v_O_2556_);
v___x_2593_ = lean_int_div(v_a_2585_, v_a_2584_);
lean_dec(v_a_2584_);
v___x_2594_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2593_);
v___x_2595_ = lean_apply_2(v_leq_2592_, v___x_2594_, v_a_2583_);
v___x_2596_ = lp_kanon_Kanon_whenSome___redArg(v___x_2586_, v___x_2595_);
return v___x_2596_;
}
else
{
lean_object* v_leq_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_leq_2597_ = lean_ctor_get(v_O_2556_, 16);
lean_inc_ref(v_leq_2597_);
lean_dec_ref(v_O_2556_);
v___x_2598_ = lean_int_div(v_a_2585_, v_a_2584_);
lean_dec(v_a_2584_);
v___x_2599_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2598_);
v___x_2600_ = lean_apply_2(v_leq_2597_, v_a_2583_, v___x_2599_);
v___x_2601_ = lp_kanon_Kanon_whenSome___redArg(v___x_2586_, v___x_2600_);
return v___x_2601_;
}
}
else
{
v___y_2560_ = v_a_2584_;
v___y_2561_ = v___x_2587_;
v___y_2562_ = v_a_2583_;
v___y_2563_ = v___x_2586_;
v___y_2564_ = v_a_2585_;
goto v___jp_2559_;
}
}
else
{
v___y_2560_ = v_a_2584_;
v___y_2561_ = v___x_2587_;
v___y_2562_ = v_a_2583_;
v___y_2563_ = v___x_2586_;
v___y_2564_ = v_a_2585_;
goto v___jp_2559_;
}
}
else
{
uint8_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec_ref(v_O_2556_);
v___x_2602_ = lean_int_dec_lt(v___x_2587_, v_a_2585_);
v___x_2603_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_2602_);
v___x_2604_ = lp_kanon_Kanon_whenSome___redArg(v___x_2586_, v___x_2603_);
return v___x_2604_;
}
}
else
{
lean_dec_ref_known(v_kind_2581_, 1);
lean_dec_ref_known(v_kind_2576_, 2);
lean_dec_ref(v_O_2556_);
return v___y_2578_;
}
}
else
{
lean_dec_ref(v_kind_2581_);
lean_dec_ref_known(v_kind_2576_, 2);
lean_dec_ref(v_O_2556_);
return v___y_2578_;
}
}
else
{
lean_dec_ref_known(v_kind_2576_, 2);
lean_dec_ref(v_O_2556_);
return v___y_2578_;
}
}
else
{
lean_dec_ref(v_kind_2576_);
lean_dec_ref(v_O_2556_);
return v___y_2578_;
}
}
v___jp_2605_:
{
if (lean_obj_tag(v___y_2606_) == 0)
{
v___y_2578_ = v___y_2606_;
goto v___jp_2577_;
}
else
{
lean_dec_ref(v_kind_2576_);
lean_dec_ref(v_O_2556_);
return v___y_2606_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mul__const___boxed(lean_object* v_O_2649_, lean_object* v_v1_2650_, lean_object* v_v2_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = lp_kanon__tiny__values_Tiny_lt_r__mul__const(v_O_2649_, v_v1_2650_, v_v2_2651_);
lean_dec_ref(v_v2_2651_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(lean_object* v_a_2653_, lean_object* v_a_2654_, uint8_t v_ty_2655_, uint8_t v_ty_2656_, lean_object* v_b_2657_, uint8_t v_ty_2658_){
_start:
{
lean_object* v___x_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2659_ = lp_kanon__tiny__values_Tiny_abs(v_a_2654_);
v___x_2660_ = lean_int_dec_le(v___x_2659_, v_b_2657_);
lean_dec(v___x_2659_);
v___x_2661_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_2662_ = lp_kanon_Kanon_whenSome___redArg(v___x_2660_, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0___boxed(lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_ty_2665_, lean_object* v_ty_2666_, lean_object* v_b_2667_, lean_object* v_ty_2668_){
_start:
{
uint8_t v_ty_231__boxed_2669_; uint8_t v_ty_232__boxed_2670_; uint8_t v_ty_233__boxed_2671_; lean_object* v_res_2672_; 
v_ty_231__boxed_2669_ = lean_unbox(v_ty_2665_);
v_ty_232__boxed_2670_ = lean_unbox(v_ty_2666_);
v_ty_233__boxed_2671_ = lean_unbox(v_ty_2668_);
v_res_2672_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(v_a_2663_, v_a_2664_, v_ty_231__boxed_2669_, v_ty_232__boxed_2670_, v_b_2667_, v_ty_233__boxed_2671_);
lean_dec(v_b_2667_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg(lean_object* v_v1_2673_, lean_object* v_v2_2674_){
_start:
{
lean_object* v_kind_2675_; uint8_t v_ty_2676_; lean_object* v___y_2678_; 
v_kind_2675_ = lean_ctor_get(v_v1_2673_, 0);
v_ty_2676_ = lean_ctor_get_uint8(v_v1_2673_, sizeof(void*)*1);
if (lean_obj_tag(v_kind_2675_) == 2)
{
uint8_t v_a_2689_; 
v_a_2689_ = lean_ctor_get_uint8(v_kind_2675_, sizeof(void*)*2);
if (v_a_2689_ == 10)
{
lean_object* v_a_2690_; lean_object* v_kind_2691_; 
v_a_2690_ = lean_ctor_get(v_kind_2675_, 1);
v_kind_2691_ = lean_ctor_get(v_a_2690_, 0);
if (lean_obj_tag(v_kind_2691_) == 6)
{
lean_object* v_kind_2692_; 
v_kind_2692_ = lean_ctor_get(v_v2_2674_, 0);
if (lean_obj_tag(v_kind_2692_) == 6)
{
lean_object* v_a_2693_; uint8_t v_ty_2694_; lean_object* v_a_2695_; uint8_t v_ty_2696_; lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2693_ = lean_ctor_get(v_kind_2675_, 0);
v_ty_2694_ = lean_ctor_get_uint8(v_a_2690_, sizeof(void*)*1);
v_a_2695_ = lean_ctor_get(v_kind_2691_, 0);
v_ty_2696_ = lean_ctor_get_uint8(v_v2_2674_, sizeof(void*)*1);
v_a_2697_ = lean_ctor_get(v_kind_2692_, 0);
v___x_2698_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(v_a_2693_, v_a_2695_, v_ty_2694_, v_ty_2676_, v_a_2697_, v_ty_2696_);
if (lean_obj_tag(v___x_2698_) == 0)
{
v___y_2678_ = v___x_2698_;
goto v___jp_2677_;
}
else
{
return v___x_2698_;
}
}
else
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_box(0);
v___y_2678_ = v___x_2699_;
goto v___jp_2677_;
}
}
else
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_box(0);
v___y_2678_ = v___x_2700_;
goto v___jp_2677_;
}
}
else
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_box(0);
v___y_2678_ = v___x_2701_;
goto v___jp_2677_;
}
}
else
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_box(0);
v___y_2678_ = v___x_2702_;
goto v___jp_2677_;
}
v___jp_2677_:
{
if (lean_obj_tag(v_kind_2675_) == 2)
{
uint8_t v_a_2679_; 
v_a_2679_ = lean_ctor_get_uint8(v_kind_2675_, sizeof(void*)*2);
if (v_a_2679_ == 9)
{
lean_object* v_a_2680_; lean_object* v_kind_2681_; 
v_a_2680_ = lean_ctor_get(v_kind_2675_, 1);
v_kind_2681_ = lean_ctor_get(v_a_2680_, 0);
if (lean_obj_tag(v_kind_2681_) == 6)
{
lean_object* v_kind_2682_; 
v_kind_2682_ = lean_ctor_get(v_v2_2674_, 0);
if (lean_obj_tag(v_kind_2682_) == 6)
{
lean_object* v_a_2683_; uint8_t v_ty_2684_; lean_object* v_a_2685_; uint8_t v_ty_2686_; lean_object* v_a_2687_; lean_object* v___x_2688_; 
lean_dec(v___y_2678_);
v_a_2683_ = lean_ctor_get(v_kind_2675_, 0);
v_ty_2684_ = lean_ctor_get_uint8(v_a_2680_, sizeof(void*)*1);
v_a_2685_ = lean_ctor_get(v_kind_2681_, 0);
v_ty_2686_ = lean_ctor_get_uint8(v_v2_2674_, sizeof(void*)*1);
v_a_2687_ = lean_ctor_get(v_kind_2682_, 0);
v___x_2688_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(v_a_2683_, v_a_2685_, v_ty_2684_, v_ty_2676_, v_a_2687_, v_ty_2686_);
return v___x_2688_;
}
else
{
return v___y_2678_;
}
}
else
{
return v___y_2678_;
}
}
else
{
return v___y_2678_;
}
}
else
{
return v___y_2678_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___boxed(lean_object* v_v1_2703_, lean_object* v_v2_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg(v_v1_2703_, v_v2_2704_);
lean_dec_ref(v_v2_2704_);
lean_dec_ref(v_v1_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const(lean_object* v_O_2706_, lean_object* v_v1_2707_, lean_object* v_v2_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg(v_v1_2707_, v_v2_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__mod__const___boxed(lean_object* v_O_2710_, lean_object* v_v1_2711_, lean_object* v_v2_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const(v_O_2710_, v_v1_2711_, v_v2_2712_);
lean_dec_ref(v_v2_2712_);
lean_dec_ref(v_v1_2711_);
lean_dec_ref(v_O_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0(lean_object* v_b_2714_, uint8_t v_ty_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, uint8_t v_ty_2718_, uint8_t v_ty_2719_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2720_ = lp_kanon__tiny__values_Tiny_abs(v_a_2717_);
v___x_2721_ = lean_int_neg(v___x_2720_);
lean_dec(v___x_2720_);
v___x_2722_ = lean_int_dec_lt(v_b_2714_, v___x_2721_);
lean_dec(v___x_2721_);
v___x_2723_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_2724_ = lp_kanon_Kanon_whenSome___redArg(v___x_2722_, v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0___boxed(lean_object* v_b_2725_, lean_object* v_ty_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_ty_2729_, lean_object* v_ty_2730_){
_start:
{
uint8_t v_ty_240__boxed_2731_; uint8_t v_ty_242__boxed_2732_; uint8_t v_ty_243__boxed_2733_; lean_object* v_res_2734_; 
v_ty_240__boxed_2731_ = lean_unbox(v_ty_2726_);
v_ty_242__boxed_2732_ = lean_unbox(v_ty_2729_);
v_ty_243__boxed_2733_ = lean_unbox(v_ty_2730_);
v_res_2734_ = lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0(v_b_2725_, v_ty_240__boxed_2731_, v_a_2727_, v_a_2728_, v_ty_242__boxed_2732_, v_ty_243__boxed_2733_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_b_2725_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg(lean_object* v_v1_2735_, lean_object* v_v2_2736_){
_start:
{
lean_object* v_kind_2737_; uint8_t v_ty_2738_; lean_object* v___y_2740_; 
v_kind_2737_ = lean_ctor_get(v_v1_2735_, 0);
v_ty_2738_ = lean_ctor_get_uint8(v_v1_2735_, sizeof(void*)*1);
if (lean_obj_tag(v_kind_2737_) == 6)
{
lean_object* v_kind_2751_; 
v_kind_2751_ = lean_ctor_get(v_v2_2736_, 0);
if (lean_obj_tag(v_kind_2751_) == 2)
{
uint8_t v_a_2752_; 
v_a_2752_ = lean_ctor_get_uint8(v_kind_2751_, sizeof(void*)*2);
if (v_a_2752_ == 10)
{
lean_object* v_a_2753_; lean_object* v_kind_2754_; 
v_a_2753_ = lean_ctor_get(v_kind_2751_, 1);
v_kind_2754_ = lean_ctor_get(v_a_2753_, 0);
if (lean_obj_tag(v_kind_2754_) == 6)
{
lean_object* v_a_2755_; uint8_t v_ty_2756_; lean_object* v_a_2757_; uint8_t v_ty_2758_; lean_object* v_a_2759_; lean_object* v___x_2760_; 
v_a_2755_ = lean_ctor_get(v_kind_2737_, 0);
v_ty_2756_ = lean_ctor_get_uint8(v_v2_2736_, sizeof(void*)*1);
v_a_2757_ = lean_ctor_get(v_kind_2751_, 0);
v_ty_2758_ = lean_ctor_get_uint8(v_a_2753_, sizeof(void*)*1);
v_a_2759_ = lean_ctor_get(v_kind_2754_, 0);
v___x_2760_ = lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0(v_a_2755_, v_ty_2738_, v_a_2757_, v_a_2759_, v_ty_2758_, v_ty_2756_);
if (lean_obj_tag(v___x_2760_) == 0)
{
v___y_2740_ = v___x_2760_;
goto v___jp_2739_;
}
else
{
return v___x_2760_;
}
}
else
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_box(0);
v___y_2740_ = v___x_2761_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_box(0);
v___y_2740_ = v___x_2762_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_box(0);
v___y_2740_ = v___x_2763_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_box(0);
v___y_2740_ = v___x_2764_;
goto v___jp_2739_;
}
v___jp_2739_:
{
if (lean_obj_tag(v_kind_2737_) == 6)
{
lean_object* v_kind_2741_; 
v_kind_2741_ = lean_ctor_get(v_v2_2736_, 0);
if (lean_obj_tag(v_kind_2741_) == 2)
{
uint8_t v_a_2742_; 
v_a_2742_ = lean_ctor_get_uint8(v_kind_2741_, sizeof(void*)*2);
if (v_a_2742_ == 9)
{
lean_object* v_a_2743_; lean_object* v_kind_2744_; 
v_a_2743_ = lean_ctor_get(v_kind_2741_, 1);
v_kind_2744_ = lean_ctor_get(v_a_2743_, 0);
if (lean_obj_tag(v_kind_2744_) == 6)
{
lean_object* v_a_2745_; uint8_t v_ty_2746_; lean_object* v_a_2747_; uint8_t v_ty_2748_; lean_object* v_a_2749_; lean_object* v___x_2750_; 
lean_dec(v___y_2740_);
v_a_2745_ = lean_ctor_get(v_kind_2737_, 0);
v_ty_2746_ = lean_ctor_get_uint8(v_v2_2736_, sizeof(void*)*1);
v_a_2747_ = lean_ctor_get(v_kind_2741_, 0);
v_ty_2748_ = lean_ctor_get_uint8(v_a_2743_, sizeof(void*)*1);
v_a_2749_ = lean_ctor_get(v_kind_2744_, 0);
v___x_2750_ = lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___lam__0(v_a_2745_, v_ty_2738_, v_a_2747_, v_a_2749_, v_ty_2748_, v_ty_2746_);
return v___x_2750_;
}
else
{
return v___y_2740_;
}
}
else
{
return v___y_2740_;
}
}
else
{
return v___y_2740_;
}
}
else
{
return v___y_2740_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg___boxed(lean_object* v_v1_2765_, lean_object* v_v2_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg(v_v1_2765_, v_v2_2766_);
lean_dec_ref(v_v2_2766_);
lean_dec_ref(v_v1_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod(lean_object* v_O_2768_, lean_object* v_v1_2769_, lean_object* v_v2_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = lp_kanon__tiny__values_Tiny_lt_r__const__mod___redArg(v_v1_2769_, v_v2_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__mod___boxed(lean_object* v_O_2772_, lean_object* v_v1_2773_, lean_object* v_v2_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = lp_kanon__tiny__values_Tiny_lt_r__const__mod(v_O_2772_, v_v1_2773_, v_v2_2774_);
lean_dec_ref(v_v2_2774_);
lean_dec_ref(v_v1_2773_);
lean_dec_ref(v_O_2772_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__const__ite(lean_object* v_O_2776_, lean_object* v_v1_2777_, lean_object* v_v2_2778_){
_start:
{
lean_object* v_kind_2779_; 
v_kind_2779_ = lean_ctor_get(v_v1_2777_, 0);
if (lean_obj_tag(v_kind_2779_) == 6)
{
lean_object* v_kind_2780_; 
v_kind_2780_ = lean_ctor_get(v_v2_2778_, 0);
lean_inc_ref(v_kind_2780_);
lean_dec_ref(v_v2_2778_);
if (lean_obj_tag(v_kind_2780_) == 5)
{
lean_object* v_a_2781_; lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v_b__ite_2784_; lean_object* v_lt_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2781_ = lean_ctor_get(v_kind_2780_, 0);
lean_inc_ref(v_a_2781_);
v_a_2782_ = lean_ctor_get(v_kind_2780_, 1);
lean_inc_ref(v_a_2782_);
v_a_2783_ = lean_ctor_get(v_kind_2780_, 2);
lean_inc_ref(v_a_2783_);
lean_dec_ref_known(v_kind_2780_, 3);
v_b__ite_2784_ = lean_ctor_get(v_O_2776_, 4);
lean_inc_ref(v_b__ite_2784_);
v_lt_2785_ = lean_ctor_get(v_O_2776_, 15);
lean_inc_ref_n(v_lt_2785_, 2);
lean_dec_ref(v_O_2776_);
v___x_2786_ = 1;
lean_inc_ref(v_v1_2777_);
v___x_2787_ = lean_apply_2(v_lt_2785_, v_v1_2777_, v_a_2782_);
v___x_2788_ = lean_apply_2(v_lt_2785_, v_v1_2777_, v_a_2783_);
v___x_2789_ = lean_apply_3(v_b__ite_2784_, v_a_2781_, v___x_2787_, v___x_2788_);
v___x_2790_ = lp_kanon_Kanon_whenSome___redArg(v___x_2786_, v___x_2789_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; 
lean_dec_ref(v_kind_2780_);
lean_dec_ref(v_v1_2777_);
lean_dec_ref(v_O_2776_);
v___x_2791_ = lean_box(0);
return v___x_2791_;
}
}
else
{
lean_object* v___x_2792_; 
lean_dec_ref(v_v2_2778_);
lean_dec_ref(v_v1_2777_);
lean_dec_ref(v_O_2776_);
v___x_2792_ = lean_box(0);
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__ite__const(lean_object* v_O_2793_, lean_object* v_v1_2794_, lean_object* v_v2_2795_){
_start:
{
lean_object* v_kind_2796_; 
v_kind_2796_ = lean_ctor_get(v_v1_2794_, 0);
lean_inc_ref(v_kind_2796_);
lean_dec_ref(v_v1_2794_);
if (lean_obj_tag(v_kind_2796_) == 5)
{
lean_object* v_kind_2797_; 
v_kind_2797_ = lean_ctor_get(v_v2_2795_, 0);
if (lean_obj_tag(v_kind_2797_) == 6)
{
lean_object* v_a_2798_; lean_object* v_a_2799_; lean_object* v_a_2800_; lean_object* v_b__ite_2801_; lean_object* v_lt_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2798_ = lean_ctor_get(v_kind_2796_, 0);
lean_inc_ref(v_a_2798_);
v_a_2799_ = lean_ctor_get(v_kind_2796_, 1);
lean_inc_ref(v_a_2799_);
v_a_2800_ = lean_ctor_get(v_kind_2796_, 2);
lean_inc_ref(v_a_2800_);
lean_dec_ref_known(v_kind_2796_, 3);
v_b__ite_2801_ = lean_ctor_get(v_O_2793_, 4);
lean_inc_ref(v_b__ite_2801_);
v_lt_2802_ = lean_ctor_get(v_O_2793_, 15);
lean_inc_ref_n(v_lt_2802_, 2);
lean_dec_ref(v_O_2793_);
v___x_2803_ = 1;
lean_inc_ref(v_v2_2795_);
v___x_2804_ = lean_apply_2(v_lt_2802_, v_a_2799_, v_v2_2795_);
v___x_2805_ = lean_apply_2(v_lt_2802_, v_a_2800_, v_v2_2795_);
v___x_2806_ = lean_apply_3(v_b__ite_2801_, v_a_2798_, v___x_2804_, v___x_2805_);
v___x_2807_ = lp_kanon_Kanon_whenSome___redArg(v___x_2803_, v___x_2806_);
return v___x_2807_;
}
else
{
lean_object* v___x_2808_; 
lean_dec_ref_known(v_kind_2796_, 3);
lean_dec_ref(v_v2_2795_);
lean_dec_ref(v_O_2793_);
v___x_2808_ = lean_box(0);
return v___x_2808_;
}
}
else
{
lean_object* v___x_2809_; 
lean_dec_ref(v_kind_2796_);
lean_dec_ref(v_v2_2795_);
lean_dec_ref(v_O_2793_);
v___x_2809_ = lean_box(0);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__default___redArg(lean_object* v_v1_2810_, lean_object* v_v2_2811_){
_start:
{
uint8_t v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2812_ = 1;
v___x_2813_ = 4;
v___x_2814_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2814_, 0, v_v1_2810_);
lean_ctor_set(v___x_2814_, 1, v_v2_2811_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*2, v___x_2813_);
v___x_2815_ = 0;
v___x_2816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set_uint8(v___x_2816_, sizeof(void*)*1, v___x_2815_);
v___x_2817_ = lp_kanon_Kanon_whenSome___redArg(v___x_2812_, v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__default(lean_object* v_O_2818_, lean_object* v_v1_2819_, lean_object* v_v2_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = lp_kanon__tiny__values_Tiny_lt_r__default___redArg(v_v1_2819_, v_v2_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_lt_r__default___boxed(lean_object* v_O_2822_, lean_object* v_v1_2823_, lean_object* v_v2_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = lp_kanon__tiny__values_Tiny_lt_r__default(v_O_2822_, v_v1_2823_, v_v2_2824_);
lean_dec_ref(v_O_2822_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits___redArg(lean_object* v_v1_2826_, lean_object* v_v2_2827_){
_start:
{
lean_object* v_kind_2828_; 
v_kind_2828_ = lean_ctor_get(v_v1_2826_, 0);
if (lean_obj_tag(v_kind_2828_) == 6)
{
lean_object* v_kind_2829_; 
v_kind_2829_ = lean_ctor_get(v_v2_2827_, 0);
if (lean_obj_tag(v_kind_2829_) == 6)
{
lean_object* v_a_2830_; lean_object* v_a_2831_; uint8_t v___x_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_a_2830_ = lean_ctor_get(v_kind_2828_, 0);
v_a_2831_ = lean_ctor_get(v_kind_2829_, 0);
v___x_2832_ = 1;
v___x_2833_ = lean_int_dec_le(v_a_2830_, v_a_2831_);
v___x_2834_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_2833_);
v___x_2835_ = lp_kanon_Kanon_whenSome___redArg(v___x_2832_, v___x_2834_);
return v___x_2835_;
}
else
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_box(0);
return v___x_2836_;
}
}
else
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_box(0);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits___redArg___boxed(lean_object* v_v1_2838_, lean_object* v_v2_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = lp_kanon__tiny__values_Tiny_leq_r__lits___redArg(v_v1_2838_, v_v2_2839_);
lean_dec_ref(v_v2_2839_);
lean_dec_ref(v_v1_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits(lean_object* v_O_2841_, lean_object* v_v1_2842_, lean_object* v_v2_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = lp_kanon__tiny__values_Tiny_leq_r__lits___redArg(v_v1_2842_, v_v2_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__lits___boxed(lean_object* v_O_2845_, lean_object* v_v1_2846_, lean_object* v_v2_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = lp_kanon__tiny__values_Tiny_leq_r__lits(v_O_2845_, v_v1_2846_, v_v2_2847_);
lean_dec_ref(v_v2_2847_);
lean_dec_ref(v_v1_2846_);
lean_dec_ref(v_O_2845_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__add__const(lean_object* v_O_2849_, lean_object* v_v1_2850_, lean_object* v_v2_2851_){
_start:
{
lean_object* v_kind_2852_; lean_object* v___y_2854_; 
v_kind_2852_ = lean_ctor_get(v_v1_2850_, 0);
lean_inc_ref(v_kind_2852_);
lean_dec_ref(v_v1_2850_);
if (lean_obj_tag(v_kind_2852_) == 2)
{
uint8_t v_a_2868_; 
v_a_2868_ = lean_ctor_get_uint8(v_kind_2852_, sizeof(void*)*2);
if (v_a_2868_ == 5)
{
lean_object* v_a_2869_; lean_object* v_kind_2870_; 
v_a_2869_ = lean_ctor_get(v_kind_2852_, 1);
v_kind_2870_ = lean_ctor_get(v_a_2869_, 0);
if (lean_obj_tag(v_kind_2870_) == 6)
{
lean_object* v_kind_2871_; 
v_kind_2871_ = lean_ctor_get(v_v2_2851_, 0);
if (lean_obj_tag(v_kind_2871_) == 6)
{
lean_object* v_a_2872_; lean_object* v_a_2873_; lean_object* v_a_2874_; lean_object* v_leq_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_a_2872_ = lean_ctor_get(v_kind_2852_, 0);
v_a_2873_ = lean_ctor_get(v_kind_2870_, 0);
v_a_2874_ = lean_ctor_get(v_kind_2871_, 0);
v_leq_2875_ = lean_ctor_get(v_O_2849_, 16);
v___x_2876_ = 1;
v___x_2877_ = lean_int_sub(v_a_2874_, v_a_2873_);
v___x_2878_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2877_);
lean_inc_ref(v_leq_2875_);
lean_inc_ref(v_a_2872_);
v___x_2879_ = lean_apply_2(v_leq_2875_, v_a_2872_, v___x_2878_);
v___x_2880_ = lp_kanon_Kanon_whenSome___redArg(v___x_2876_, v___x_2879_);
if (lean_obj_tag(v___x_2880_) == 0)
{
v___y_2854_ = v___x_2880_;
goto v___jp_2853_;
}
else
{
lean_dec_ref_known(v_kind_2852_, 2);
lean_dec_ref(v_O_2849_);
return v___x_2880_;
}
}
else
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_box(0);
v___y_2854_ = v___x_2881_;
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_box(0);
v___y_2854_ = v___x_2882_;
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_box(0);
v___y_2854_ = v___x_2883_;
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_box(0);
v___y_2854_ = v___x_2884_;
goto v___jp_2853_;
}
v___jp_2853_:
{
if (lean_obj_tag(v_kind_2852_) == 2)
{
uint8_t v_a_2855_; 
v_a_2855_ = lean_ctor_get_uint8(v_kind_2852_, sizeof(void*)*2);
if (v_a_2855_ == 5)
{
lean_object* v_a_2856_; lean_object* v_kind_2857_; 
v_a_2856_ = lean_ctor_get(v_kind_2852_, 0);
v_kind_2857_ = lean_ctor_get(v_a_2856_, 0);
lean_inc_ref(v_kind_2857_);
if (lean_obj_tag(v_kind_2857_) == 6)
{
lean_object* v_kind_2858_; 
v_kind_2858_ = lean_ctor_get(v_v2_2851_, 0);
if (lean_obj_tag(v_kind_2858_) == 6)
{
lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v_a_2861_; lean_object* v_leq_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec(v___y_2854_);
v_a_2859_ = lean_ctor_get(v_kind_2852_, 1);
lean_inc_ref(v_a_2859_);
lean_dec_ref_known(v_kind_2852_, 2);
v_a_2860_ = lean_ctor_get(v_kind_2857_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v_kind_2857_, 1);
v_a_2861_ = lean_ctor_get(v_kind_2858_, 0);
v_leq_2862_ = lean_ctor_get(v_O_2849_, 16);
lean_inc_ref(v_leq_2862_);
lean_dec_ref(v_O_2849_);
v___x_2863_ = 1;
v___x_2864_ = lean_int_sub(v_a_2861_, v_a_2860_);
lean_dec(v_a_2860_);
v___x_2865_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2864_);
v___x_2866_ = lean_apply_2(v_leq_2862_, v_a_2859_, v___x_2865_);
v___x_2867_ = lp_kanon_Kanon_whenSome___redArg(v___x_2863_, v___x_2866_);
return v___x_2867_;
}
else
{
lean_dec_ref_known(v_kind_2857_, 1);
lean_dec_ref_known(v_kind_2852_, 2);
lean_dec_ref(v_O_2849_);
return v___y_2854_;
}
}
else
{
lean_dec_ref(v_kind_2857_);
lean_dec_ref_known(v_kind_2852_, 2);
lean_dec_ref(v_O_2849_);
return v___y_2854_;
}
}
else
{
lean_dec_ref_known(v_kind_2852_, 2);
lean_dec_ref(v_O_2849_);
return v___y_2854_;
}
}
else
{
lean_dec_ref(v_kind_2852_);
lean_dec_ref(v_O_2849_);
return v___y_2854_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__add__const___boxed(lean_object* v_O_2885_, lean_object* v_v1_2886_, lean_object* v_v2_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = lp_kanon__tiny__values_Tiny_leq_r__add__const(v_O_2885_, v_v1_2886_, v_v2_2887_);
lean_dec_ref(v_v2_2887_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__add(lean_object* v_O_2889_, lean_object* v_v1_2890_, lean_object* v_v2_2891_){
_start:
{
lean_object* v_kind_2892_; lean_object* v___y_2894_; 
v_kind_2892_ = lean_ctor_get(v_v1_2890_, 0);
if (lean_obj_tag(v_kind_2892_) == 6)
{
lean_object* v_kind_2908_; 
v_kind_2908_ = lean_ctor_get(v_v2_2891_, 0);
if (lean_obj_tag(v_kind_2908_) == 2)
{
uint8_t v_a_2909_; 
v_a_2909_ = lean_ctor_get_uint8(v_kind_2908_, sizeof(void*)*2);
if (v_a_2909_ == 5)
{
lean_object* v_a_2910_; lean_object* v_kind_2911_; 
v_a_2910_ = lean_ctor_get(v_kind_2908_, 1);
v_kind_2911_ = lean_ctor_get(v_a_2910_, 0);
if (lean_obj_tag(v_kind_2911_) == 6)
{
lean_object* v_a_2912_; lean_object* v_a_2913_; lean_object* v_a_2914_; lean_object* v_leq_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2912_ = lean_ctor_get(v_kind_2892_, 0);
v_a_2913_ = lean_ctor_get(v_kind_2908_, 0);
v_a_2914_ = lean_ctor_get(v_kind_2911_, 0);
v_leq_2915_ = lean_ctor_get(v_O_2889_, 16);
v___x_2916_ = 1;
v___x_2917_ = lean_int_sub(v_a_2912_, v_a_2914_);
v___x_2918_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2917_);
lean_inc_ref(v_leq_2915_);
lean_inc_ref(v_a_2913_);
v___x_2919_ = lean_apply_2(v_leq_2915_, v___x_2918_, v_a_2913_);
v___x_2920_ = lp_kanon_Kanon_whenSome___redArg(v___x_2916_, v___x_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
v___y_2894_ = v___x_2920_;
goto v___jp_2893_;
}
else
{
lean_dec_ref(v_v2_2891_);
lean_dec_ref(v_O_2889_);
return v___x_2920_;
}
}
else
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_box(0);
v___y_2894_ = v___x_2921_;
goto v___jp_2893_;
}
}
else
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_box(0);
v___y_2894_ = v___x_2922_;
goto v___jp_2893_;
}
}
else
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_box(0);
v___y_2894_ = v___x_2923_;
goto v___jp_2893_;
}
}
else
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_box(0);
v___y_2894_ = v___x_2924_;
goto v___jp_2893_;
}
v___jp_2893_:
{
if (lean_obj_tag(v_kind_2892_) == 6)
{
lean_object* v_kind_2895_; 
v_kind_2895_ = lean_ctor_get(v_v2_2891_, 0);
lean_inc_ref(v_kind_2895_);
lean_dec_ref(v_v2_2891_);
if (lean_obj_tag(v_kind_2895_) == 2)
{
uint8_t v_a_2896_; 
v_a_2896_ = lean_ctor_get_uint8(v_kind_2895_, sizeof(void*)*2);
if (v_a_2896_ == 5)
{
lean_object* v_a_2897_; lean_object* v_kind_2898_; 
v_a_2897_ = lean_ctor_get(v_kind_2895_, 0);
v_kind_2898_ = lean_ctor_get(v_a_2897_, 0);
lean_inc_ref(v_kind_2898_);
if (lean_obj_tag(v_kind_2898_) == 6)
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v_a_2901_; lean_object* v_leq_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec(v___y_2894_);
v_a_2899_ = lean_ctor_get(v_kind_2892_, 0);
v_a_2900_ = lean_ctor_get(v_kind_2895_, 1);
lean_inc_ref(v_a_2900_);
lean_dec_ref_known(v_kind_2895_, 2);
v_a_2901_ = lean_ctor_get(v_kind_2898_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v_kind_2898_, 1);
v_leq_2902_ = lean_ctor_get(v_O_2889_, 16);
lean_inc_ref(v_leq_2902_);
lean_dec_ref(v_O_2889_);
v___x_2903_ = 1;
v___x_2904_ = lean_int_sub(v_a_2899_, v_a_2901_);
lean_dec(v_a_2901_);
v___x_2905_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2904_);
v___x_2906_ = lean_apply_2(v_leq_2902_, v___x_2905_, v_a_2900_);
v___x_2907_ = lp_kanon_Kanon_whenSome___redArg(v___x_2903_, v___x_2906_);
return v___x_2907_;
}
else
{
lean_dec_ref(v_kind_2898_);
lean_dec_ref_known(v_kind_2895_, 2);
lean_dec_ref(v_O_2889_);
return v___y_2894_;
}
}
else
{
lean_dec_ref_known(v_kind_2895_, 2);
lean_dec_ref(v_O_2889_);
return v___y_2894_;
}
}
else
{
lean_dec_ref(v_kind_2895_);
lean_dec_ref(v_O_2889_);
return v___y_2894_;
}
}
else
{
lean_dec_ref(v_v2_2891_);
lean_dec_ref(v_O_2889_);
return v___y_2894_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__add___boxed(lean_object* v_O_2925_, lean_object* v_v1_2926_, lean_object* v_v2_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = lp_kanon__tiny__values_Tiny_leq_r__const__add(v_O_2925_, v_v1_2926_, v_v2_2927_);
lean_dec_ref(v_v1_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__sub__const(lean_object* v_O_2929_, lean_object* v_v1_2930_, lean_object* v_v2_2931_){
_start:
{
lean_object* v_kind_2932_; 
v_kind_2932_ = lean_ctor_get(v_v1_2930_, 0);
lean_inc_ref(v_kind_2932_);
lean_dec_ref(v_v1_2930_);
if (lean_obj_tag(v_kind_2932_) == 2)
{
uint8_t v_a_2933_; 
v_a_2933_ = lean_ctor_get_uint8(v_kind_2932_, sizeof(void*)*2);
if (v_a_2933_ == 6)
{
lean_object* v_a_2934_; lean_object* v_kind_2935_; 
v_a_2934_ = lean_ctor_get(v_kind_2932_, 1);
v_kind_2935_ = lean_ctor_get(v_a_2934_, 0);
lean_inc_ref(v_kind_2935_);
if (lean_obj_tag(v_kind_2935_) == 6)
{
lean_object* v_kind_2936_; 
v_kind_2936_ = lean_ctor_get(v_v2_2931_, 0);
if (lean_obj_tag(v_kind_2936_) == 6)
{
lean_object* v_a_2937_; lean_object* v_a_2938_; lean_object* v_a_2939_; lean_object* v_leq_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_a_2937_ = lean_ctor_get(v_kind_2932_, 0);
lean_inc_ref(v_a_2937_);
lean_dec_ref_known(v_kind_2932_, 2);
v_a_2938_ = lean_ctor_get(v_kind_2935_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v_kind_2935_, 1);
v_a_2939_ = lean_ctor_get(v_kind_2936_, 0);
v_leq_2940_ = lean_ctor_get(v_O_2929_, 16);
lean_inc_ref(v_leq_2940_);
lean_dec_ref(v_O_2929_);
v___x_2941_ = 1;
v___x_2942_ = lean_int_add(v_a_2939_, v_a_2938_);
lean_dec(v_a_2938_);
v___x_2943_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2942_);
v___x_2944_ = lean_apply_2(v_leq_2940_, v_a_2937_, v___x_2943_);
v___x_2945_ = lp_kanon_Kanon_whenSome___redArg(v___x_2941_, v___x_2944_);
return v___x_2945_;
}
else
{
lean_object* v___x_2946_; 
lean_dec_ref_known(v_kind_2935_, 1);
lean_dec_ref_known(v_kind_2932_, 2);
lean_dec_ref(v_O_2929_);
v___x_2946_ = lean_box(0);
return v___x_2946_;
}
}
else
{
lean_object* v___x_2947_; 
lean_dec_ref(v_kind_2935_);
lean_dec_ref_known(v_kind_2932_, 2);
lean_dec_ref(v_O_2929_);
v___x_2947_ = lean_box(0);
return v___x_2947_;
}
}
else
{
lean_object* v___x_2948_; 
lean_dec_ref_known(v_kind_2932_, 2);
lean_dec_ref(v_O_2929_);
v___x_2948_ = lean_box(0);
return v___x_2948_;
}
}
else
{
lean_object* v___x_2949_; 
lean_dec_ref(v_kind_2932_);
lean_dec_ref(v_O_2929_);
v___x_2949_ = lean_box(0);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__sub__const___boxed(lean_object* v_O_2950_, lean_object* v_v1_2951_, lean_object* v_v2_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = lp_kanon__tiny__values_Tiny_leq_r__sub__const(v_O_2950_, v_v1_2951_, v_v2_2952_);
lean_dec_ref(v_v2_2952_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__rsub__const(lean_object* v_O_2954_, lean_object* v_v1_2955_, lean_object* v_v2_2956_){
_start:
{
lean_object* v_kind_2957_; 
v_kind_2957_ = lean_ctor_get(v_v1_2955_, 0);
lean_inc_ref(v_kind_2957_);
lean_dec_ref(v_v1_2955_);
if (lean_obj_tag(v_kind_2957_) == 2)
{
uint8_t v_a_2958_; 
v_a_2958_ = lean_ctor_get_uint8(v_kind_2957_, sizeof(void*)*2);
if (v_a_2958_ == 6)
{
lean_object* v_a_2959_; lean_object* v_kind_2960_; 
v_a_2959_ = lean_ctor_get(v_kind_2957_, 0);
v_kind_2960_ = lean_ctor_get(v_a_2959_, 0);
lean_inc_ref(v_kind_2960_);
if (lean_obj_tag(v_kind_2960_) == 6)
{
lean_object* v_kind_2961_; 
v_kind_2961_ = lean_ctor_get(v_v2_2956_, 0);
if (lean_obj_tag(v_kind_2961_) == 6)
{
lean_object* v_a_2962_; lean_object* v_a_2963_; lean_object* v_a_2964_; lean_object* v_leq_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_a_2962_ = lean_ctor_get(v_kind_2957_, 1);
lean_inc_ref(v_a_2962_);
lean_dec_ref_known(v_kind_2957_, 2);
v_a_2963_ = lean_ctor_get(v_kind_2960_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v_kind_2960_, 1);
v_a_2964_ = lean_ctor_get(v_kind_2961_, 0);
v_leq_2965_ = lean_ctor_get(v_O_2954_, 16);
lean_inc_ref(v_leq_2965_);
lean_dec_ref(v_O_2954_);
v___x_2966_ = 1;
v___x_2967_ = lean_int_sub(v_a_2963_, v_a_2964_);
lean_dec(v_a_2963_);
v___x_2968_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2967_);
v___x_2969_ = lean_apply_2(v_leq_2965_, v___x_2968_, v_a_2962_);
v___x_2970_ = lp_kanon_Kanon_whenSome___redArg(v___x_2966_, v___x_2969_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; 
lean_dec_ref_known(v_kind_2960_, 1);
lean_dec_ref_known(v_kind_2957_, 2);
lean_dec_ref(v_O_2954_);
v___x_2971_ = lean_box(0);
return v___x_2971_;
}
}
else
{
lean_object* v___x_2972_; 
lean_dec_ref(v_kind_2960_);
lean_dec_ref_known(v_kind_2957_, 2);
lean_dec_ref(v_O_2954_);
v___x_2972_ = lean_box(0);
return v___x_2972_;
}
}
else
{
lean_object* v___x_2973_; 
lean_dec_ref_known(v_kind_2957_, 2);
lean_dec_ref(v_O_2954_);
v___x_2973_ = lean_box(0);
return v___x_2973_;
}
}
else
{
lean_object* v___x_2974_; 
lean_dec_ref(v_kind_2957_);
lean_dec_ref(v_O_2954_);
v___x_2974_ = lean_box(0);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__rsub__const___boxed(lean_object* v_O_2975_, lean_object* v_v1_2976_, lean_object* v_v2_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = lp_kanon__tiny__values_Tiny_leq_r__rsub__const(v_O_2975_, v_v1_2976_, v_v2_2977_);
lean_dec_ref(v_v2_2977_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__sub(lean_object* v_O_2979_, lean_object* v_v1_2980_, lean_object* v_v2_2981_){
_start:
{
lean_object* v_kind_2982_; 
v_kind_2982_ = lean_ctor_get(v_v1_2980_, 0);
if (lean_obj_tag(v_kind_2982_) == 6)
{
lean_object* v_kind_2983_; 
v_kind_2983_ = lean_ctor_get(v_v2_2981_, 0);
lean_inc_ref(v_kind_2983_);
lean_dec_ref(v_v2_2981_);
if (lean_obj_tag(v_kind_2983_) == 2)
{
uint8_t v_a_2984_; 
v_a_2984_ = lean_ctor_get_uint8(v_kind_2983_, sizeof(void*)*2);
if (v_a_2984_ == 6)
{
lean_object* v_a_2985_; lean_object* v_kind_2986_; 
v_a_2985_ = lean_ctor_get(v_kind_2983_, 1);
v_kind_2986_ = lean_ctor_get(v_a_2985_, 0);
lean_inc_ref(v_kind_2986_);
if (lean_obj_tag(v_kind_2986_) == 6)
{
lean_object* v_a_2987_; lean_object* v_a_2988_; lean_object* v_a_2989_; lean_object* v_leq_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2987_ = lean_ctor_get(v_kind_2982_, 0);
v_a_2988_ = lean_ctor_get(v_kind_2983_, 0);
lean_inc_ref(v_a_2988_);
lean_dec_ref_known(v_kind_2983_, 2);
v_a_2989_ = lean_ctor_get(v_kind_2986_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v_kind_2986_, 1);
v_leq_2990_ = lean_ctor_get(v_O_2979_, 16);
lean_inc_ref(v_leq_2990_);
lean_dec_ref(v_O_2979_);
v___x_2991_ = 1;
v___x_2992_ = lean_int_add(v_a_2987_, v_a_2989_);
lean_dec(v_a_2989_);
v___x_2993_ = lp_kanon__tiny__values_Tiny_int__z(v___x_2992_);
v___x_2994_ = lean_apply_2(v_leq_2990_, v___x_2993_, v_a_2988_);
v___x_2995_ = lp_kanon_Kanon_whenSome___redArg(v___x_2991_, v___x_2994_);
return v___x_2995_;
}
else
{
lean_object* v___x_2996_; 
lean_dec_ref(v_kind_2986_);
lean_dec_ref_known(v_kind_2983_, 2);
lean_dec_ref(v_O_2979_);
v___x_2996_ = lean_box(0);
return v___x_2996_;
}
}
else
{
lean_object* v___x_2997_; 
lean_dec_ref_known(v_kind_2983_, 2);
lean_dec_ref(v_O_2979_);
v___x_2997_ = lean_box(0);
return v___x_2997_;
}
}
else
{
lean_object* v___x_2998_; 
lean_dec_ref(v_kind_2983_);
lean_dec_ref(v_O_2979_);
v___x_2998_ = lean_box(0);
return v___x_2998_;
}
}
else
{
lean_object* v___x_2999_; 
lean_dec_ref(v_v2_2981_);
lean_dec_ref(v_O_2979_);
v___x_2999_ = lean_box(0);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__sub___boxed(lean_object* v_O_3000_, lean_object* v_v1_3001_, lean_object* v_v2_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = lp_kanon__tiny__values_Tiny_leq_r__const__sub(v_O_3000_, v_v1_3001_, v_v2_3002_);
lean_dec_ref(v_v1_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rsub(lean_object* v_O_3004_, lean_object* v_v1_3005_, lean_object* v_v2_3006_){
_start:
{
lean_object* v_kind_3007_; 
v_kind_3007_ = lean_ctor_get(v_v1_3005_, 0);
if (lean_obj_tag(v_kind_3007_) == 6)
{
lean_object* v_kind_3008_; 
v_kind_3008_ = lean_ctor_get(v_v2_3006_, 0);
lean_inc_ref(v_kind_3008_);
lean_dec_ref(v_v2_3006_);
if (lean_obj_tag(v_kind_3008_) == 2)
{
uint8_t v_a_3009_; 
v_a_3009_ = lean_ctor_get_uint8(v_kind_3008_, sizeof(void*)*2);
if (v_a_3009_ == 6)
{
lean_object* v_a_3010_; lean_object* v_kind_3011_; 
v_a_3010_ = lean_ctor_get(v_kind_3008_, 0);
v_kind_3011_ = lean_ctor_get(v_a_3010_, 0);
lean_inc_ref(v_kind_3011_);
if (lean_obj_tag(v_kind_3011_) == 6)
{
lean_object* v_a_3012_; lean_object* v_a_3013_; lean_object* v_a_3014_; lean_object* v_leq_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3012_ = lean_ctor_get(v_kind_3007_, 0);
v_a_3013_ = lean_ctor_get(v_kind_3008_, 1);
lean_inc_ref(v_a_3013_);
lean_dec_ref_known(v_kind_3008_, 2);
v_a_3014_ = lean_ctor_get(v_kind_3011_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v_kind_3011_, 1);
v_leq_3015_ = lean_ctor_get(v_O_3004_, 16);
lean_inc_ref(v_leq_3015_);
lean_dec_ref(v_O_3004_);
v___x_3016_ = 1;
v___x_3017_ = lean_int_sub(v_a_3014_, v_a_3012_);
lean_dec(v_a_3014_);
v___x_3018_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3017_);
v___x_3019_ = lean_apply_2(v_leq_3015_, v_a_3013_, v___x_3018_);
v___x_3020_ = lp_kanon_Kanon_whenSome___redArg(v___x_3016_, v___x_3019_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
lean_dec_ref(v_kind_3011_);
lean_dec_ref_known(v_kind_3008_, 2);
lean_dec_ref(v_O_3004_);
v___x_3021_ = lean_box(0);
return v___x_3021_;
}
}
else
{
lean_object* v___x_3022_; 
lean_dec_ref_known(v_kind_3008_, 2);
lean_dec_ref(v_O_3004_);
v___x_3022_ = lean_box(0);
return v___x_3022_;
}
}
else
{
lean_object* v___x_3023_; 
lean_dec_ref(v_kind_3008_);
lean_dec_ref(v_O_3004_);
v___x_3023_ = lean_box(0);
return v___x_3023_;
}
}
else
{
lean_object* v___x_3024_; 
lean_dec_ref(v_v2_3006_);
lean_dec_ref(v_O_3004_);
v___x_3024_ = lean_box(0);
return v___x_3024_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rsub___boxed(lean_object* v_O_3025_, lean_object* v_v1_3026_, lean_object* v_v2_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = lp_kanon__tiny__values_Tiny_leq_r__const__rsub(v_O_3025_, v_v1_3026_, v_v2_3027_);
lean_dec_ref(v_v1_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mul(lean_object* v_O_3029_, lean_object* v_v1_3030_, lean_object* v_v2_3031_){
_start:
{
lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v_kind_3049_; lean_object* v___y_3051_; lean_object* v___y_3079_; 
v_kind_3049_ = lean_ctor_get(v_v1_3030_, 0);
if (lean_obj_tag(v_kind_3049_) == 6)
{
lean_object* v_kind_3080_; 
v_kind_3080_ = lean_ctor_get(v_v2_3031_, 0);
if (lean_obj_tag(v_kind_3080_) == 2)
{
uint8_t v_a_3081_; 
v_a_3081_ = lean_ctor_get_uint8(v_kind_3080_, sizeof(void*)*2);
if (v_a_3081_ == 7)
{
lean_object* v_a_3082_; lean_object* v_kind_3083_; 
v_a_3082_ = lean_ctor_get(v_kind_3080_, 0);
v_kind_3083_ = lean_ctor_get(v_a_3082_, 0);
if (lean_obj_tag(v_kind_3083_) == 6)
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v_a_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3101_; 
v_a_3084_ = lean_ctor_get(v_kind_3049_, 0);
v_a_3085_ = lean_ctor_get(v_kind_3080_, 1);
v_a_3086_ = lean_ctor_get(v_kind_3083_, 0);
v___x_3087_ = 1;
v___x_3088_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_3101_ = lean_int_dec_eq(v_a_3086_, v___x_3088_);
if (v___x_3101_ == 0)
{
uint8_t v___x_3102_; 
v___x_3102_ = l_Int_decidableDvd(v_a_3086_, v_a_3084_);
if (v___x_3102_ == 0)
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_int_dec_lt(v_a_3084_, v___x_3088_);
if (v___x_3103_ == 0)
{
uint8_t v___x_3104_; 
v___x_3104_ = lean_int_dec_lt(v___x_3088_, v_a_3086_);
if (v___x_3104_ == 0)
{
lean_object* v_lt_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_lt_3105_ = lean_ctor_get(v_O_3029_, 15);
v___x_3106_ = lean_int_div(v_a_3084_, v_a_3086_);
v___x_3107_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3106_);
lean_inc_ref(v_lt_3105_);
lean_inc_ref(v_a_3085_);
v___x_3108_ = lean_apply_2(v_lt_3105_, v_a_3085_, v___x_3107_);
v___x_3109_ = lp_kanon_Kanon_whenSome___redArg(v___x_3087_, v___x_3108_);
v___y_3079_ = v___x_3109_;
goto v___jp_3078_;
}
else
{
lean_object* v_lt_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_lt_3110_ = lean_ctor_get(v_O_3029_, 15);
v___x_3111_ = lean_int_div(v_a_3084_, v_a_3086_);
v___x_3112_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3111_);
lean_inc_ref(v_lt_3110_);
lean_inc_ref(v_a_3085_);
v___x_3113_ = lean_apply_2(v_lt_3110_, v___x_3112_, v_a_3085_);
v___x_3114_ = lp_kanon_Kanon_whenSome___redArg(v___x_3087_, v___x_3113_);
v___y_3079_ = v___x_3114_;
goto v___jp_3078_;
}
}
else
{
goto v___jp_3089_;
}
}
else
{
goto v___jp_3089_;
}
}
else
{
uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_int_dec_le(v_a_3084_, v___x_3088_);
v___x_3116_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_3115_);
v___x_3117_ = lp_kanon_Kanon_whenSome___redArg(v___x_3087_, v___x_3116_);
v___y_3079_ = v___x_3117_;
goto v___jp_3078_;
}
v___jp_3089_:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_int_dec_lt(v___x_3088_, v_a_3086_);
if (v___x_3090_ == 0)
{
lean_object* v_leq_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_leq_3091_ = lean_ctor_get(v_O_3029_, 16);
v___x_3092_ = lean_int_div(v_a_3084_, v_a_3086_);
v___x_3093_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3092_);
lean_inc_ref(v_leq_3091_);
lean_inc_ref(v_a_3085_);
v___x_3094_ = lean_apply_2(v_leq_3091_, v_a_3085_, v___x_3093_);
v___x_3095_ = lp_kanon_Kanon_whenSome___redArg(v___x_3087_, v___x_3094_);
v___y_3079_ = v___x_3095_;
goto v___jp_3078_;
}
else
{
lean_object* v_leq_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_leq_3096_ = lean_ctor_get(v_O_3029_, 16);
v___x_3097_ = lean_int_div(v_a_3084_, v_a_3086_);
v___x_3098_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3097_);
lean_inc_ref(v_leq_3096_);
lean_inc_ref(v_a_3085_);
v___x_3099_ = lean_apply_2(v_leq_3096_, v___x_3098_, v_a_3085_);
v___x_3100_ = lp_kanon_Kanon_whenSome___redArg(v___x_3087_, v___x_3099_);
v___y_3079_ = v___x_3100_;
goto v___jp_3078_;
}
}
}
else
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_box(0);
v___y_3051_ = v___x_3118_;
goto v___jp_3050_;
}
}
else
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_box(0);
v___y_3051_ = v___x_3119_;
goto v___jp_3050_;
}
}
else
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_box(0);
v___y_3051_ = v___x_3120_;
goto v___jp_3050_;
}
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_box(0);
v___y_3051_ = v___x_3121_;
goto v___jp_3050_;
}
v___jp_3032_:
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_int_dec_lt(v___y_3033_, v___y_3037_);
if (v___x_3038_ == 0)
{
lean_object* v_leq_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_leq_3039_ = lean_ctor_get(v_O_3029_, 16);
lean_inc_ref(v_leq_3039_);
lean_dec_ref(v_O_3029_);
v___x_3040_ = lean_int_div(v___y_3034_, v___y_3037_);
lean_dec(v___y_3037_);
v___x_3041_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3040_);
v___x_3042_ = lean_apply_2(v_leq_3039_, v___y_3036_, v___x_3041_);
v___x_3043_ = lp_kanon_Kanon_whenSome___redArg(v___y_3035_, v___x_3042_);
return v___x_3043_;
}
else
{
lean_object* v_leq_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_leq_3044_ = lean_ctor_get(v_O_3029_, 16);
lean_inc_ref(v_leq_3044_);
lean_dec_ref(v_O_3029_);
v___x_3045_ = lean_int_div(v___y_3034_, v___y_3037_);
lean_dec(v___y_3037_);
v___x_3046_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3045_);
v___x_3047_ = lean_apply_2(v_leq_3044_, v___x_3046_, v___y_3036_);
v___x_3048_ = lp_kanon_Kanon_whenSome___redArg(v___y_3035_, v___x_3047_);
return v___x_3048_;
}
}
v___jp_3050_:
{
if (lean_obj_tag(v_kind_3049_) == 6)
{
lean_object* v_kind_3052_; 
v_kind_3052_ = lean_ctor_get(v_v2_3031_, 0);
lean_inc_ref(v_kind_3052_);
lean_dec_ref(v_v2_3031_);
if (lean_obj_tag(v_kind_3052_) == 2)
{
uint8_t v_a_3053_; 
v_a_3053_ = lean_ctor_get_uint8(v_kind_3052_, sizeof(void*)*2);
if (v_a_3053_ == 7)
{
lean_object* v_a_3054_; lean_object* v_kind_3055_; 
v_a_3054_ = lean_ctor_get(v_kind_3052_, 1);
v_kind_3055_ = lean_ctor_get(v_a_3054_, 0);
lean_inc_ref(v_kind_3055_);
if (lean_obj_tag(v_kind_3055_) == 6)
{
lean_object* v_a_3056_; lean_object* v_a_3057_; lean_object* v_a_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
lean_dec(v___y_3051_);
v_a_3056_ = lean_ctor_get(v_kind_3049_, 0);
v_a_3057_ = lean_ctor_get(v_kind_3052_, 0);
lean_inc_ref(v_a_3057_);
lean_dec_ref_known(v_kind_3052_, 2);
v_a_3058_ = lean_ctor_get(v_kind_3055_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v_kind_3055_, 1);
v___x_3059_ = 1;
v___x_3060_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_3061_ = lean_int_dec_eq(v_a_3058_, v___x_3060_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Int_decidableDvd(v_a_3058_, v_a_3056_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_int_dec_lt(v_a_3056_, v___x_3060_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_int_dec_lt(v___x_3060_, v_a_3058_);
if (v___x_3064_ == 0)
{
lean_object* v_lt_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_lt_3065_ = lean_ctor_get(v_O_3029_, 15);
lean_inc_ref(v_lt_3065_);
lean_dec_ref(v_O_3029_);
v___x_3066_ = lean_int_div(v_a_3056_, v_a_3058_);
lean_dec(v_a_3058_);
v___x_3067_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3066_);
v___x_3068_ = lean_apply_2(v_lt_3065_, v_a_3057_, v___x_3067_);
v___x_3069_ = lp_kanon_Kanon_whenSome___redArg(v___x_3059_, v___x_3068_);
return v___x_3069_;
}
else
{
lean_object* v_lt_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_lt_3070_ = lean_ctor_get(v_O_3029_, 15);
lean_inc_ref(v_lt_3070_);
lean_dec_ref(v_O_3029_);
v___x_3071_ = lean_int_div(v_a_3056_, v_a_3058_);
lean_dec(v_a_3058_);
v___x_3072_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3071_);
v___x_3073_ = lean_apply_2(v_lt_3070_, v___x_3072_, v_a_3057_);
v___x_3074_ = lp_kanon_Kanon_whenSome___redArg(v___x_3059_, v___x_3073_);
return v___x_3074_;
}
}
else
{
v___y_3033_ = v___x_3060_;
v___y_3034_ = v_a_3056_;
v___y_3035_ = v___x_3059_;
v___y_3036_ = v_a_3057_;
v___y_3037_ = v_a_3058_;
goto v___jp_3032_;
}
}
else
{
v___y_3033_ = v___x_3060_;
v___y_3034_ = v_a_3056_;
v___y_3035_ = v___x_3059_;
v___y_3036_ = v_a_3057_;
v___y_3037_ = v_a_3058_;
goto v___jp_3032_;
}
}
else
{
uint8_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec_ref(v_O_3029_);
v___x_3075_ = lean_int_dec_le(v_a_3056_, v___x_3060_);
v___x_3076_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_3075_);
v___x_3077_ = lp_kanon_Kanon_whenSome___redArg(v___x_3059_, v___x_3076_);
return v___x_3077_;
}
}
else
{
lean_dec_ref(v_kind_3055_);
lean_dec_ref_known(v_kind_3052_, 2);
lean_dec_ref(v_O_3029_);
return v___y_3051_;
}
}
else
{
lean_dec_ref_known(v_kind_3052_, 2);
lean_dec_ref(v_O_3029_);
return v___y_3051_;
}
}
else
{
lean_dec_ref(v_kind_3052_);
lean_dec_ref(v_O_3029_);
return v___y_3051_;
}
}
else
{
lean_dec_ref(v_v2_3031_);
lean_dec_ref(v_O_3029_);
return v___y_3051_;
}
}
v___jp_3078_:
{
if (lean_obj_tag(v___y_3079_) == 0)
{
v___y_3051_ = v___y_3079_;
goto v___jp_3050_;
}
else
{
lean_dec_ref(v_v2_3031_);
lean_dec_ref(v_O_3029_);
return v___y_3079_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mul___boxed(lean_object* v_O_3122_, lean_object* v_v1_3123_, lean_object* v_v2_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = lp_kanon__tiny__values_Tiny_leq_r__const__mul(v_O_3122_, v_v1_3123_, v_v2_3124_);
lean_dec_ref(v_v1_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mul__const(lean_object* v_O_3126_, lean_object* v_v1_3127_, lean_object* v_v2_3128_){
_start:
{
lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; uint8_t v___y_3133_; lean_object* v___y_3134_; lean_object* v_kind_3146_; lean_object* v___y_3148_; lean_object* v___y_3176_; 
v_kind_3146_ = lean_ctor_get(v_v1_3127_, 0);
lean_inc_ref(v_kind_3146_);
lean_dec_ref(v_v1_3127_);
if (lean_obj_tag(v_kind_3146_) == 2)
{
uint8_t v_a_3177_; 
v_a_3177_ = lean_ctor_get_uint8(v_kind_3146_, sizeof(void*)*2);
if (v_a_3177_ == 7)
{
lean_object* v_a_3178_; lean_object* v_kind_3179_; 
v_a_3178_ = lean_ctor_get(v_kind_3146_, 1);
v_kind_3179_ = lean_ctor_get(v_a_3178_, 0);
if (lean_obj_tag(v_kind_3179_) == 6)
{
lean_object* v_kind_3180_; 
v_kind_3180_ = lean_ctor_get(v_v2_3128_, 0);
if (lean_obj_tag(v_kind_3180_) == 6)
{
lean_object* v_a_3181_; lean_object* v_a_3182_; lean_object* v_a_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3198_; 
v_a_3181_ = lean_ctor_get(v_kind_3146_, 0);
v_a_3182_ = lean_ctor_get(v_kind_3179_, 0);
v_a_3183_ = lean_ctor_get(v_kind_3180_, 0);
v___x_3184_ = 1;
v___x_3185_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_3198_ = lean_int_dec_eq(v_a_3182_, v___x_3185_);
if (v___x_3198_ == 0)
{
uint8_t v___x_3199_; 
v___x_3199_ = l_Int_decidableDvd(v_a_3182_, v_a_3183_);
if (v___x_3199_ == 0)
{
uint8_t v___x_3200_; 
v___x_3200_ = lean_int_dec_lt(v___x_3185_, v_a_3183_);
if (v___x_3200_ == 0)
{
uint8_t v___x_3201_; 
v___x_3201_ = lean_int_dec_lt(v___x_3185_, v_a_3182_);
if (v___x_3201_ == 0)
{
lean_object* v_lt_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_lt_3202_ = lean_ctor_get(v_O_3126_, 15);
v___x_3203_ = lean_int_div(v_a_3183_, v_a_3182_);
v___x_3204_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3203_);
lean_inc_ref(v_lt_3202_);
lean_inc_ref(v_a_3181_);
v___x_3205_ = lean_apply_2(v_lt_3202_, v___x_3204_, v_a_3181_);
v___x_3206_ = lp_kanon_Kanon_whenSome___redArg(v___x_3184_, v___x_3205_);
v___y_3176_ = v___x_3206_;
goto v___jp_3175_;
}
else
{
lean_object* v_lt_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_lt_3207_ = lean_ctor_get(v_O_3126_, 15);
v___x_3208_ = lean_int_div(v_a_3183_, v_a_3182_);
v___x_3209_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3208_);
lean_inc_ref(v_lt_3207_);
lean_inc_ref(v_a_3181_);
v___x_3210_ = lean_apply_2(v_lt_3207_, v_a_3181_, v___x_3209_);
v___x_3211_ = lp_kanon_Kanon_whenSome___redArg(v___x_3184_, v___x_3210_);
v___y_3176_ = v___x_3211_;
goto v___jp_3175_;
}
}
else
{
goto v___jp_3186_;
}
}
else
{
goto v___jp_3186_;
}
}
else
{
uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_int_dec_le(v___x_3185_, v_a_3183_);
v___x_3213_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_3212_);
v___x_3214_ = lp_kanon_Kanon_whenSome___redArg(v___x_3184_, v___x_3213_);
v___y_3176_ = v___x_3214_;
goto v___jp_3175_;
}
v___jp_3186_:
{
uint8_t v___x_3187_; 
v___x_3187_ = lean_int_dec_lt(v___x_3185_, v_a_3182_);
if (v___x_3187_ == 0)
{
lean_object* v_leq_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_leq_3188_ = lean_ctor_get(v_O_3126_, 16);
v___x_3189_ = lean_int_div(v_a_3183_, v_a_3182_);
v___x_3190_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3189_);
lean_inc_ref(v_leq_3188_);
lean_inc_ref(v_a_3181_);
v___x_3191_ = lean_apply_2(v_leq_3188_, v___x_3190_, v_a_3181_);
v___x_3192_ = lp_kanon_Kanon_whenSome___redArg(v___x_3184_, v___x_3191_);
v___y_3176_ = v___x_3192_;
goto v___jp_3175_;
}
else
{
lean_object* v_leq_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_leq_3193_ = lean_ctor_get(v_O_3126_, 16);
v___x_3194_ = lean_int_div(v_a_3183_, v_a_3182_);
v___x_3195_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3194_);
lean_inc_ref(v_leq_3193_);
lean_inc_ref(v_a_3181_);
v___x_3196_ = lean_apply_2(v_leq_3193_, v_a_3181_, v___x_3195_);
v___x_3197_ = lp_kanon_Kanon_whenSome___redArg(v___x_3184_, v___x_3196_);
v___y_3176_ = v___x_3197_;
goto v___jp_3175_;
}
}
}
else
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_box(0);
v___y_3148_ = v___x_3215_;
goto v___jp_3147_;
}
}
else
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_box(0);
v___y_3148_ = v___x_3216_;
goto v___jp_3147_;
}
}
else
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_box(0);
v___y_3148_ = v___x_3217_;
goto v___jp_3147_;
}
}
else
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_box(0);
v___y_3148_ = v___x_3218_;
goto v___jp_3147_;
}
v___jp_3129_:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_int_dec_lt(v___y_3131_, v___y_3130_);
if (v___x_3135_ == 0)
{
lean_object* v_leq_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_leq_3136_ = lean_ctor_get(v_O_3126_, 16);
lean_inc_ref(v_leq_3136_);
lean_dec_ref(v_O_3126_);
v___x_3137_ = lean_int_div(v___y_3134_, v___y_3130_);
lean_dec(v___y_3130_);
v___x_3138_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3137_);
v___x_3139_ = lean_apply_2(v_leq_3136_, v___x_3138_, v___y_3132_);
v___x_3140_ = lp_kanon_Kanon_whenSome___redArg(v___y_3133_, v___x_3139_);
return v___x_3140_;
}
else
{
lean_object* v_leq_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_leq_3141_ = lean_ctor_get(v_O_3126_, 16);
lean_inc_ref(v_leq_3141_);
lean_dec_ref(v_O_3126_);
v___x_3142_ = lean_int_div(v___y_3134_, v___y_3130_);
lean_dec(v___y_3130_);
v___x_3143_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3142_);
v___x_3144_ = lean_apply_2(v_leq_3141_, v___y_3132_, v___x_3143_);
v___x_3145_ = lp_kanon_Kanon_whenSome___redArg(v___y_3133_, v___x_3144_);
return v___x_3145_;
}
}
v___jp_3147_:
{
if (lean_obj_tag(v_kind_3146_) == 2)
{
uint8_t v_a_3149_; 
v_a_3149_ = lean_ctor_get_uint8(v_kind_3146_, sizeof(void*)*2);
if (v_a_3149_ == 7)
{
lean_object* v_a_3150_; lean_object* v_kind_3151_; 
v_a_3150_ = lean_ctor_get(v_kind_3146_, 0);
v_kind_3151_ = lean_ctor_get(v_a_3150_, 0);
lean_inc_ref(v_kind_3151_);
if (lean_obj_tag(v_kind_3151_) == 6)
{
lean_object* v_kind_3152_; 
v_kind_3152_ = lean_ctor_get(v_v2_3128_, 0);
if (lean_obj_tag(v_kind_3152_) == 6)
{
lean_object* v_a_3153_; lean_object* v_a_3154_; lean_object* v_a_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
lean_dec(v___y_3148_);
v_a_3153_ = lean_ctor_get(v_kind_3146_, 1);
lean_inc_ref(v_a_3153_);
lean_dec_ref_known(v_kind_3146_, 2);
v_a_3154_ = lean_ctor_get(v_kind_3151_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v_kind_3151_, 1);
v_a_3155_ = lean_ctor_get(v_kind_3152_, 0);
v___x_3156_ = 1;
v___x_3157_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_3158_ = lean_int_dec_eq(v_a_3154_, v___x_3157_);
if (v___x_3158_ == 0)
{
uint8_t v___x_3159_; 
v___x_3159_ = l_Int_decidableDvd(v_a_3154_, v_a_3155_);
if (v___x_3159_ == 0)
{
uint8_t v___x_3160_; 
v___x_3160_ = lean_int_dec_lt(v___x_3157_, v_a_3155_);
if (v___x_3160_ == 0)
{
uint8_t v___x_3161_; 
v___x_3161_ = lean_int_dec_lt(v___x_3157_, v_a_3154_);
if (v___x_3161_ == 0)
{
lean_object* v_lt_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v_lt_3162_ = lean_ctor_get(v_O_3126_, 15);
lean_inc_ref(v_lt_3162_);
lean_dec_ref(v_O_3126_);
v___x_3163_ = lean_int_div(v_a_3155_, v_a_3154_);
lean_dec(v_a_3154_);
v___x_3164_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3163_);
v___x_3165_ = lean_apply_2(v_lt_3162_, v___x_3164_, v_a_3153_);
v___x_3166_ = lp_kanon_Kanon_whenSome___redArg(v___x_3156_, v___x_3165_);
return v___x_3166_;
}
else
{
lean_object* v_lt_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_lt_3167_ = lean_ctor_get(v_O_3126_, 15);
lean_inc_ref(v_lt_3167_);
lean_dec_ref(v_O_3126_);
v___x_3168_ = lean_int_div(v_a_3155_, v_a_3154_);
lean_dec(v_a_3154_);
v___x_3169_ = lp_kanon__tiny__values_Tiny_int__z(v___x_3168_);
v___x_3170_ = lean_apply_2(v_lt_3167_, v_a_3153_, v___x_3169_);
v___x_3171_ = lp_kanon_Kanon_whenSome___redArg(v___x_3156_, v___x_3170_);
return v___x_3171_;
}
}
else
{
v___y_3130_ = v_a_3154_;
v___y_3131_ = v___x_3157_;
v___y_3132_ = v_a_3153_;
v___y_3133_ = v___x_3156_;
v___y_3134_ = v_a_3155_;
goto v___jp_3129_;
}
}
else
{
v___y_3130_ = v_a_3154_;
v___y_3131_ = v___x_3157_;
v___y_3132_ = v_a_3153_;
v___y_3133_ = v___x_3156_;
v___y_3134_ = v_a_3155_;
goto v___jp_3129_;
}
}
else
{
uint8_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec_ref(v_O_3126_);
v___x_3172_ = lean_int_dec_le(v___x_3157_, v_a_3155_);
v___x_3173_ = lp_kanon__tiny__values_Tiny_of__bool(v___x_3172_);
v___x_3174_ = lp_kanon_Kanon_whenSome___redArg(v___x_3156_, v___x_3173_);
return v___x_3174_;
}
}
else
{
lean_dec_ref_known(v_kind_3151_, 1);
lean_dec_ref_known(v_kind_3146_, 2);
lean_dec_ref(v_O_3126_);
return v___y_3148_;
}
}
else
{
lean_dec_ref(v_kind_3151_);
lean_dec_ref_known(v_kind_3146_, 2);
lean_dec_ref(v_O_3126_);
return v___y_3148_;
}
}
else
{
lean_dec_ref_known(v_kind_3146_, 2);
lean_dec_ref(v_O_3126_);
return v___y_3148_;
}
}
else
{
lean_dec_ref(v_kind_3146_);
lean_dec_ref(v_O_3126_);
return v___y_3148_;
}
}
v___jp_3175_:
{
if (lean_obj_tag(v___y_3176_) == 0)
{
v___y_3148_ = v___y_3176_;
goto v___jp_3147_;
}
else
{
lean_dec_ref(v_kind_3146_);
lean_dec_ref(v_O_3126_);
return v___y_3176_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mul__const___boxed(lean_object* v_O_3219_, lean_object* v_v1_3220_, lean_object* v_v2_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = lp_kanon__tiny__values_Tiny_leq_r__mul__const(v_O_3219_, v_v1_3220_, v_v2_3221_);
lean_dec_ref(v_v2_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const___redArg(lean_object* v_v1_3223_, lean_object* v_v2_3224_){
_start:
{
lean_object* v_kind_3225_; uint8_t v_ty_3226_; lean_object* v___y_3228_; 
v_kind_3225_ = lean_ctor_get(v_v1_3223_, 0);
v_ty_3226_ = lean_ctor_get_uint8(v_v1_3223_, sizeof(void*)*1);
if (lean_obj_tag(v_kind_3225_) == 2)
{
uint8_t v_a_3239_; 
v_a_3239_ = lean_ctor_get_uint8(v_kind_3225_, sizeof(void*)*2);
if (v_a_3239_ == 10)
{
lean_object* v_a_3240_; lean_object* v_kind_3241_; 
v_a_3240_ = lean_ctor_get(v_kind_3225_, 1);
v_kind_3241_ = lean_ctor_get(v_a_3240_, 0);
if (lean_obj_tag(v_kind_3241_) == 6)
{
lean_object* v_kind_3242_; 
v_kind_3242_ = lean_ctor_get(v_v2_3224_, 0);
if (lean_obj_tag(v_kind_3242_) == 6)
{
lean_object* v_a_3243_; uint8_t v_ty_3244_; lean_object* v_a_3245_; uint8_t v_ty_3246_; lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3243_ = lean_ctor_get(v_kind_3225_, 0);
v_ty_3244_ = lean_ctor_get_uint8(v_a_3240_, sizeof(void*)*1);
v_a_3245_ = lean_ctor_get(v_kind_3241_, 0);
v_ty_3246_ = lean_ctor_get_uint8(v_v2_3224_, sizeof(void*)*1);
v_a_3247_ = lean_ctor_get(v_kind_3242_, 0);
v___x_3248_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(v_a_3243_, v_a_3245_, v_ty_3244_, v_ty_3226_, v_a_3247_, v_ty_3246_);
if (lean_obj_tag(v___x_3248_) == 0)
{
v___y_3228_ = v___x_3248_;
goto v___jp_3227_;
}
else
{
return v___x_3248_;
}
}
else
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_box(0);
v___y_3228_ = v___x_3249_;
goto v___jp_3227_;
}
}
else
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_box(0);
v___y_3228_ = v___x_3250_;
goto v___jp_3227_;
}
}
else
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_box(0);
v___y_3228_ = v___x_3251_;
goto v___jp_3227_;
}
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_box(0);
v___y_3228_ = v___x_3252_;
goto v___jp_3227_;
}
v___jp_3227_:
{
if (lean_obj_tag(v_kind_3225_) == 2)
{
uint8_t v_a_3229_; 
v_a_3229_ = lean_ctor_get_uint8(v_kind_3225_, sizeof(void*)*2);
if (v_a_3229_ == 9)
{
lean_object* v_a_3230_; lean_object* v_kind_3231_; 
v_a_3230_ = lean_ctor_get(v_kind_3225_, 1);
v_kind_3231_ = lean_ctor_get(v_a_3230_, 0);
if (lean_obj_tag(v_kind_3231_) == 6)
{
lean_object* v_kind_3232_; 
v_kind_3232_ = lean_ctor_get(v_v2_3224_, 0);
if (lean_obj_tag(v_kind_3232_) == 6)
{
lean_object* v_a_3233_; uint8_t v_ty_3234_; lean_object* v_a_3235_; uint8_t v_ty_3236_; lean_object* v_a_3237_; lean_object* v___x_3238_; 
lean_dec(v___y_3228_);
v_a_3233_ = lean_ctor_get(v_kind_3225_, 0);
v_ty_3234_ = lean_ctor_get_uint8(v_a_3230_, sizeof(void*)*1);
v_a_3235_ = lean_ctor_get(v_kind_3231_, 0);
v_ty_3236_ = lean_ctor_get_uint8(v_v2_3224_, sizeof(void*)*1);
v_a_3237_ = lean_ctor_get(v_kind_3232_, 0);
v___x_3238_ = lp_kanon__tiny__values_Tiny_lt_r__mod__const___redArg___lam__0(v_a_3233_, v_a_3235_, v_ty_3234_, v_ty_3226_, v_a_3237_, v_ty_3236_);
return v___x_3238_;
}
else
{
return v___y_3228_;
}
}
else
{
return v___y_3228_;
}
}
else
{
return v___y_3228_;
}
}
else
{
return v___y_3228_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const___redArg___boxed(lean_object* v_v1_3253_, lean_object* v_v2_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = lp_kanon__tiny__values_Tiny_leq_r__mod__const___redArg(v_v1_3253_, v_v2_3254_);
lean_dec_ref(v_v2_3254_);
lean_dec_ref(v_v1_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const(lean_object* v_O_3256_, lean_object* v_v1_3257_, lean_object* v_v2_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = lp_kanon__tiny__values_Tiny_leq_r__mod__const___redArg(v_v1_3257_, v_v2_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__mod__const___boxed(lean_object* v_O_3260_, lean_object* v_v1_3261_, lean_object* v_v2_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = lp_kanon__tiny__values_Tiny_leq_r__mod__const(v_O_3260_, v_v1_3261_, v_v2_3262_);
lean_dec_ref(v_v2_3262_);
lean_dec_ref(v_v1_3261_);
lean_dec_ref(v_O_3260_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem___redArg(lean_object* v_v1_3264_, lean_object* v_v2_3265_){
_start:
{
lean_object* v_kind_3266_; 
v_kind_3266_ = lean_ctor_get(v_v1_3264_, 0);
if (lean_obj_tag(v_kind_3266_) == 6)
{
lean_object* v_kind_3267_; 
v_kind_3267_ = lean_ctor_get(v_v2_3265_, 0);
if (lean_obj_tag(v_kind_3267_) == 2)
{
uint8_t v_a_3268_; 
v_a_3268_ = lean_ctor_get_uint8(v_kind_3267_, sizeof(void*)*2);
if (v_a_3268_ == 9)
{
lean_object* v_a_3269_; lean_object* v_kind_3270_; 
v_a_3269_ = lean_ctor_get(v_kind_3267_, 1);
v_kind_3270_ = lean_ctor_get(v_a_3269_, 0);
if (lean_obj_tag(v_kind_3270_) == 6)
{
lean_object* v_a_3271_; lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3271_ = lean_ctor_get(v_kind_3266_, 0);
v_a_3272_ = lean_ctor_get(v_kind_3270_, 0);
v___x_3273_ = lp_kanon__tiny__values_Tiny_abs(v_a_3272_);
v___x_3274_ = lean_int_neg(v___x_3273_);
lean_dec(v___x_3273_);
v___x_3275_ = lean_int_dec_le(v_a_3271_, v___x_3274_);
lean_dec(v___x_3274_);
v___x_3276_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_3277_ = lp_kanon_Kanon_whenSome___redArg(v___x_3275_, v___x_3276_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
}
else
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_box(0);
return v___x_3279_;
}
}
else
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem___redArg___boxed(lean_object* v_v1_3282_, lean_object* v_v2_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = lp_kanon__tiny__values_Tiny_leq_r__const__rem___redArg(v_v1_3282_, v_v2_3283_);
lean_dec_ref(v_v2_3283_);
lean_dec_ref(v_v1_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem(lean_object* v_O_3285_, lean_object* v_v1_3286_, lean_object* v_v2_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = lp_kanon__tiny__values_Tiny_leq_r__const__rem___redArg(v_v1_3286_, v_v2_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__rem___boxed(lean_object* v_O_3289_, lean_object* v_v1_3290_, lean_object* v_v2_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = lp_kanon__tiny__values_Tiny_leq_r__const__rem(v_O_3289_, v_v1_3290_, v_v2_3291_);
lean_dec_ref(v_v2_3291_);
lean_dec_ref(v_v1_3290_);
lean_dec_ref(v_O_3289_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod___redArg(lean_object* v_v1_3293_, lean_object* v_v2_3294_){
_start:
{
lean_object* v_kind_3295_; 
v_kind_3295_ = lean_ctor_get(v_v1_3293_, 0);
if (lean_obj_tag(v_kind_3295_) == 6)
{
lean_object* v_kind_3296_; 
v_kind_3296_ = lean_ctor_get(v_v2_3294_, 0);
if (lean_obj_tag(v_kind_3296_) == 2)
{
uint8_t v_a_3297_; 
v_a_3297_ = lean_ctor_get_uint8(v_kind_3296_, sizeof(void*)*2);
if (v_a_3297_ == 10)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_a_3298_ = lean_ctor_get(v_kind_3295_, 0);
v___x_3299_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_abs___closed__0, &lp_kanon__tiny__values_Tiny_abs___closed__0_once, _init_lp_kanon__tiny__values_Tiny_abs___closed__0);
v___x_3300_ = lean_int_dec_le(v_a_3298_, v___x_3299_);
v___x_3301_ = lp_kanon__tiny__values_Tiny_v__true;
v___x_3302_ = lp_kanon_Kanon_whenSome___redArg(v___x_3300_, v___x_3301_);
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_box(0);
return v___x_3303_;
}
}
else
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_box(0);
return v___x_3304_;
}
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_box(0);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod___redArg___boxed(lean_object* v_v1_3306_, lean_object* v_v2_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = lp_kanon__tiny__values_Tiny_leq_r__const__mod___redArg(v_v1_3306_, v_v2_3307_);
lean_dec_ref(v_v2_3307_);
lean_dec_ref(v_v1_3306_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod(lean_object* v_O_3309_, lean_object* v_v1_3310_, lean_object* v_v2_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = lp_kanon__tiny__values_Tiny_leq_r__const__mod___redArg(v_v1_3310_, v_v2_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__mod___boxed(lean_object* v_O_3313_, lean_object* v_v1_3314_, lean_object* v_v2_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = lp_kanon__tiny__values_Tiny_leq_r__const__mod(v_O_3313_, v_v1_3314_, v_v2_3315_);
lean_dec_ref(v_v2_3315_);
lean_dec_ref(v_v1_3314_);
lean_dec_ref(v_O_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__const__ite(lean_object* v_O_3317_, lean_object* v_v1_3318_, lean_object* v_v2_3319_){
_start:
{
lean_object* v_kind_3320_; 
v_kind_3320_ = lean_ctor_get(v_v1_3318_, 0);
if (lean_obj_tag(v_kind_3320_) == 6)
{
lean_object* v_kind_3321_; 
v_kind_3321_ = lean_ctor_get(v_v2_3319_, 0);
lean_inc_ref(v_kind_3321_);
lean_dec_ref(v_v2_3319_);
if (lean_obj_tag(v_kind_3321_) == 5)
{
lean_object* v_a_3322_; lean_object* v_a_3323_; lean_object* v_a_3324_; lean_object* v_b__ite_3325_; lean_object* v_leq_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_a_3322_ = lean_ctor_get(v_kind_3321_, 0);
lean_inc_ref(v_a_3322_);
v_a_3323_ = lean_ctor_get(v_kind_3321_, 1);
lean_inc_ref(v_a_3323_);
v_a_3324_ = lean_ctor_get(v_kind_3321_, 2);
lean_inc_ref(v_a_3324_);
lean_dec_ref_known(v_kind_3321_, 3);
v_b__ite_3325_ = lean_ctor_get(v_O_3317_, 4);
lean_inc_ref(v_b__ite_3325_);
v_leq_3326_ = lean_ctor_get(v_O_3317_, 16);
lean_inc_ref_n(v_leq_3326_, 2);
lean_dec_ref(v_O_3317_);
v___x_3327_ = 1;
lean_inc_ref(v_v1_3318_);
v___x_3328_ = lean_apply_2(v_leq_3326_, v_v1_3318_, v_a_3323_);
v___x_3329_ = lean_apply_2(v_leq_3326_, v_v1_3318_, v_a_3324_);
v___x_3330_ = lean_apply_3(v_b__ite_3325_, v_a_3322_, v___x_3328_, v___x_3329_);
v___x_3331_ = lp_kanon_Kanon_whenSome___redArg(v___x_3327_, v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; 
lean_dec_ref(v_kind_3321_);
lean_dec_ref(v_v1_3318_);
lean_dec_ref(v_O_3317_);
v___x_3332_ = lean_box(0);
return v___x_3332_;
}
}
else
{
lean_object* v___x_3333_; 
lean_dec_ref(v_v2_3319_);
lean_dec_ref(v_v1_3318_);
lean_dec_ref(v_O_3317_);
v___x_3333_ = lean_box(0);
return v___x_3333_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__ite__const(lean_object* v_O_3334_, lean_object* v_v1_3335_, lean_object* v_v2_3336_){
_start:
{
lean_object* v_kind_3337_; 
v_kind_3337_ = lean_ctor_get(v_v1_3335_, 0);
lean_inc_ref(v_kind_3337_);
lean_dec_ref(v_v1_3335_);
if (lean_obj_tag(v_kind_3337_) == 5)
{
lean_object* v_kind_3338_; 
v_kind_3338_ = lean_ctor_get(v_v2_3336_, 0);
if (lean_obj_tag(v_kind_3338_) == 6)
{
lean_object* v_a_3339_; lean_object* v_a_3340_; lean_object* v_a_3341_; lean_object* v_b__ite_3342_; lean_object* v_leq_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_a_3339_ = lean_ctor_get(v_kind_3337_, 0);
lean_inc_ref(v_a_3339_);
v_a_3340_ = lean_ctor_get(v_kind_3337_, 1);
lean_inc_ref(v_a_3340_);
v_a_3341_ = lean_ctor_get(v_kind_3337_, 2);
lean_inc_ref(v_a_3341_);
lean_dec_ref_known(v_kind_3337_, 3);
v_b__ite_3342_ = lean_ctor_get(v_O_3334_, 4);
lean_inc_ref(v_b__ite_3342_);
v_leq_3343_ = lean_ctor_get(v_O_3334_, 16);
lean_inc_ref_n(v_leq_3343_, 2);
lean_dec_ref(v_O_3334_);
v___x_3344_ = 1;
lean_inc_ref(v_v2_3336_);
v___x_3345_ = lean_apply_2(v_leq_3343_, v_a_3340_, v_v2_3336_);
v___x_3346_ = lean_apply_2(v_leq_3343_, v_a_3341_, v_v2_3336_);
v___x_3347_ = lean_apply_3(v_b__ite_3342_, v_a_3339_, v___x_3345_, v___x_3346_);
v___x_3348_ = lp_kanon_Kanon_whenSome___redArg(v___x_3344_, v___x_3347_);
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; 
lean_dec_ref_known(v_kind_3337_, 3);
lean_dec_ref(v_v2_3336_);
lean_dec_ref(v_O_3334_);
v___x_3349_ = lean_box(0);
return v___x_3349_;
}
}
else
{
lean_object* v___x_3350_; 
lean_dec_ref(v_kind_3337_);
lean_dec_ref(v_v2_3336_);
lean_dec_ref(v_O_3334_);
v___x_3350_ = lean_box(0);
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__default___redArg(lean_object* v_v1_3351_, lean_object* v_v2_3352_){
_start:
{
uint8_t v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3353_ = 1;
v___x_3354_ = 3;
v___x_3355_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_3355_, 0, v_v1_3351_);
lean_ctor_set(v___x_3355_, 1, v_v2_3352_);
lean_ctor_set_uint8(v___x_3355_, sizeof(void*)*2, v___x_3354_);
v___x_3356_ = 0;
v___x_3357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*1, v___x_3356_);
v___x_3358_ = lp_kanon_Kanon_whenSome___redArg(v___x_3353_, v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__default(lean_object* v_O_3359_, lean_object* v_v1_3360_, lean_object* v_v2_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = lp_kanon__tiny__values_Tiny_leq_r__default___redArg(v_v1_3360_, v_v2_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_leq_r__default___boxed(lean_object* v_O_3363_, lean_object* v_v1_3364_, lean_object* v_v2_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = lp_kanon__tiny__values_Tiny_leq_r__default(v_O_3363_, v_v1_3364_, v_v2_3365_);
lean_dec_ref(v_O_3363_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_opsRaw(lean_object* v_orc_3383_){
_start:
{
lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___f_3386_; lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___f_3391_; lean_object* v___f_3392_; lean_object* v___f_3393_; lean_object* v___f_3394_; lean_object* v___f_3395_; lean_object* v___f_3396_; lean_object* v___f_3397_; lean_object* v___f_3398_; lean_object* v___f_3399_; lean_object* v___x_3400_; 
v___f_3384_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__0));
v___f_3385_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__1));
v___f_3386_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__2));
v___f_3387_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__3));
v___f_3388_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__4));
v___f_3389_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__5));
v___f_3390_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__6));
v___f_3391_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__7));
v___f_3392_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__8));
v___f_3393_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__9));
v___f_3394_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__10));
v___f_3395_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__11));
v___f_3396_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__12));
v___f_3397_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__13));
v___f_3398_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__14));
v___f_3399_ = ((lean_object*)(lp_kanon__tiny__values_Tiny_opsRaw___closed__15));
v___x_3400_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v___x_3400_, 0, v_orc_3383_);
lean_ctor_set(v___x_3400_, 1, v___f_3384_);
lean_ctor_set(v___x_3400_, 2, v___f_3385_);
lean_ctor_set(v___x_3400_, 3, v___f_3386_);
lean_ctor_set(v___x_3400_, 4, v___f_3387_);
lean_ctor_set(v___x_3400_, 5, v___f_3388_);
lean_ctor_set(v___x_3400_, 6, v___f_3389_);
lean_ctor_set(v___x_3400_, 7, v___f_3390_);
lean_ctor_set(v___x_3400_, 8, v___f_3391_);
lean_ctor_set(v___x_3400_, 9, v___f_3392_);
lean_ctor_set(v___x_3400_, 10, v___f_3393_);
lean_ctor_set(v___x_3400_, 11, v___f_3394_);
lean_ctor_set(v___x_3400_, 12, v___f_3395_);
lean_ctor_set(v___x_3400_, 13, v___f_3396_);
lean_ctor_set(v___x_3400_, 14, v___f_3397_);
lean_ctor_set(v___x_3400_, 15, v___f_3398_);
lean_ctor_set(v___x_3400_, 16, v___f_3399_);
return v___x_3400_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Signatures(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Model(uint8_t builtin) {
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
res = initialize_kanon__tiny__values_Tiny_Signatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
