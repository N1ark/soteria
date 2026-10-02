// Lean compiler output
// Module: Tiny.Prims
// Imports: public import Init public meta import Init public import KanonCore public import Tiny.Syntax
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_ty(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_ty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_kind(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_kind___boxed(lean_object*);
static const lean_ctor_object lp_kanon__tiny__values_Tiny_v__true___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 4}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_v__true___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_v__true___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_v__true___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_v__true___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_v__true___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_v__true___closed__1_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_v__true = (const lean_object*)&lp_kanon__tiny__values_Tiny_v__true___closed__1_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_v__false___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 4}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_v__false___closed__0 = (const lean_object*)&lp_kanon__tiny__values_Tiny_v__false___closed__0_value;
static const lean_ctor_object lp_kanon__tiny__values_Tiny_v__false___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_kanon__tiny__values_Tiny_v__false___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_kanon__tiny__values_Tiny_v__false___closed__1 = (const lean_object*)&lp_kanon__tiny__values_Tiny_v__false___closed__1_value;
LEAN_EXPORT const lean_object* lp_kanon__tiny__values_Tiny_v__false = (const lean_object*)&lp_kanon__tiny__values_Tiny_v__false___closed__1_value;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_int__z(lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_zero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_zero___closed__0;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_zero___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_zero___closed__1;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_zero;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_one___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_one___closed__0;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_one___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_one___closed__1;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_one;
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_var__equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_var__equal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_tdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_tdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_trem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_trem___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_divisible(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_divisible___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_ediv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_erem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_erem___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_ty(lean_object* v_v_1_){
_start:
{
uint8_t v_ty_2_; 
v_ty_2_ = lean_ctor_get_uint8(v_v_1_, sizeof(void*)*1);
return v_ty_2_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_ty___boxed(lean_object* v_v_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = lp_kanon__tiny__values_Tiny_ty(v_v_3_);
lean_dec_ref(v_v_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_kind(lean_object* v_v_6_){
_start:
{
lean_object* v_kind_7_; 
v_kind_7_ = lean_ctor_get(v_v_6_, 0);
lean_inc_ref(v_kind_7_);
return v_kind_7_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_kind___boxed(lean_object* v_v_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_kanon__tiny__values_Tiny_kind(v_v_8_);
lean_dec_ref(v_v_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_int__z(lean_object* v_z_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_23_, 0, v_z_22_);
v___x_24_ = 1;
v___x_25_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_25_, 0, v___x_23_);
lean_ctor_set_uint8(v___x_25_, sizeof(void*)*1, v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_zero___closed__0(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_nat_to_int(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_zero___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_zero___closed__0, &lp_kanon__tiny__values_Tiny_zero___closed__0_once, _init_lp_kanon__tiny__values_Tiny_zero___closed__0);
v___x_29_ = lp_kanon__tiny__values_Tiny_int__z(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_zero(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_zero___closed__1, &lp_kanon__tiny__values_Tiny_zero___closed__1_once, _init_lp_kanon__tiny__values_Tiny_zero___closed__1);
return v___x_30_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_one___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_to_int(v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_one___closed__1(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_one___closed__0, &lp_kanon__tiny__values_Tiny_one___closed__0_once, _init_lp_kanon__tiny__values_Tiny_one___closed__0);
v___x_34_ = lp_kanon__tiny__values_Tiny_int__z(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_one(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_one___closed__1, &lp_kanon__tiny__values_Tiny_one___closed__1_once, _init_lp_kanon__tiny__values_Tiny_one___closed__1);
return v___x_35_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_var__equal(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_int_dec_eq(v_a_36_, v_b_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_var__equal___boxed(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = lp_kanon__tiny__values_Tiny_var__equal(v_a_39_, v_b_40_);
lean_dec(v_b_40_);
lean_dec(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_tdiv(lean_object* v_a_43_, lean_object* v_b_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_int_div(v_a_43_, v_b_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_tdiv___boxed(lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_kanon__tiny__values_Tiny_tdiv(v_a_46_, v_b_47_);
lean_dec(v_b_47_);
lean_dec(v_a_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_trem(lean_object* v_a_49_, lean_object* v_b_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_int_mod(v_a_49_, v_b_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_trem___boxed(lean_object* v_a_52_, lean_object* v_b_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_kanon__tiny__values_Tiny_trem(v_a_52_, v_b_53_);
lean_dec(v_b_53_);
lean_dec(v_a_52_);
return v_res_54_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_divisible(lean_object* v_a_55_, lean_object* v_b_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = l_Int_decidableDvd(v_b_56_, v_a_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_divisible___boxed(lean_object* v_a_58_, lean_object* v_b_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = lp_kanon__tiny__values_Tiny_divisible(v_a_58_, v_b_59_);
lean_dec(v_b_59_);
lean_dec(v_a_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_ediv(lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_int_ediv(v_a_62_, v_b_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_ediv___boxed(lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = lp_kanon__tiny__values_Tiny_ediv(v_a_65_, v_b_66_);
lean_dec(v_b_66_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_erem(lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_int_emod(v_a_68_, v_b_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_erem___boxed(lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = lp_kanon__tiny__values_Tiny_erem(v_a_71_, v_b_72_);
lean_dec(v_b_72_);
lean_dec(v_a_71_);
return v_res_73_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_kanon_KanonCore(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Syntax(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Prims(uint8_t builtin) {
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
res = initialize_kanon_KanonCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_kanon__tiny__values_Tiny_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_kanon__tiny__values_Tiny_zero = _init_lp_kanon__tiny__values_Tiny_zero();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_zero);
lp_kanon__tiny__values_Tiny_one = _init_lp_kanon__tiny__values_Tiny_one();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_one);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
