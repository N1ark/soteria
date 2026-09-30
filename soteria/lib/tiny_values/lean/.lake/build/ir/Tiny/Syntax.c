// Lean compiler output
// Module: Tiny.Syntax
// Imports: public import Init public meta import Init public import Tiny.Abstract
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
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Unop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Unop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Binop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Binop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Nop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Nop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Bool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Bool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Ite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Ite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Int_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Int_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Term_kind(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Term_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Term_ty(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Term_ty___boxed(lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__0;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instInhabitedKind;
static lean_once_cell_t lp_kanon__tiny__values_Tiny_instInhabitedTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_instInhabitedTerm___closed__0;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instInhabitedTerm;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_kanon__tiny__values_Tiny_Kind_ctorIdx(v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 1:
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_14_);
lean_dec_ref_known(v_t_11_, 2);
v___x_15_ = lean_apply_2(v_k_12_, v_a_13_, v_a_14_);
return v___x_15_;
}
case 2:
{
uint8_t v_a_16_; lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_a_16_ = lean_ctor_get_uint8(v_t_11_, sizeof(void*)*2);
v_a_17_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_17_);
v_a_18_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_18_);
lean_dec_ref_known(v_t_11_, 2);
v___x_19_ = lean_box(v_a_16_);
v___x_20_ = lean_apply_3(v_k_12_, v___x_19_, v_a_17_, v_a_18_);
return v___x_20_;
}
case 3:
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_21_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_22_);
lean_dec_ref_known(v_t_11_, 2);
v___x_23_ = lean_apply_2(v_k_12_, v_a_21_, v_a_22_);
return v___x_23_;
}
case 4:
{
uint8_t v_a_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_a_24_ = lean_ctor_get_uint8(v_t_11_, 0);
lean_dec_ref_known(v_t_11_, 0);
v___x_25_ = lean_box(v_a_24_);
v___x_26_ = lean_apply_1(v_k_12_, v___x_25_);
return v___x_26_;
}
case 5:
{
lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_27_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_27_);
v_a_28_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_a_28_);
v_a_29_ = lean_ctor_get(v_t_11_, 2);
lean_inc_ref(v_a_29_);
lean_dec_ref_known(v_t_11_, 3);
v___x_30_ = lean_apply_3(v_k_12_, v_a_27_, v_a_28_, v_a_29_);
return v___x_30_;
}
default: 
{
lean_object* v_a_31_; lean_object* v___x_32_; 
v_a_31_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_t_11_);
v___x_32_ = lean_apply_1(v_k_12_, v_a_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorElim(lean_object* v_motive__1_33_, lean_object* v_ctorIdx_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_k_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_35_, v_k_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_ctorElim___boxed(lean_object* v_motive__1_39_, lean_object* v_ctorIdx_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_k_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim(v_motive__1_39_, v_ctorIdx_40_, v_t_41_, v_h_42_, v_k_43_);
lean_dec(v_ctorIdx_40_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Var_elim___redArg(lean_object* v_t_45_, lean_object* v_Var_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_45_, v_Var_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Var_elim(lean_object* v_motive__1_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_Var_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_49_, v_Var_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Unop_elim___redArg(lean_object* v_t_53_, lean_object* v_Unop_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_53_, v_Unop_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Unop_elim(lean_object* v_motive__1_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_Unop_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_57_, v_Unop_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Binop_elim___redArg(lean_object* v_t_61_, lean_object* v_Binop_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_61_, v_Binop_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Binop_elim(lean_object* v_motive__1_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_Binop_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_65_, v_Binop_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Nop_elim___redArg(lean_object* v_t_69_, lean_object* v_Nop_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_69_, v_Nop_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Nop_elim(lean_object* v_motive__1_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_Nop_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_73_, v_Nop_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Bool_elim___redArg(lean_object* v_t_77_, lean_object* v_Bool_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_77_, v_Bool_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Bool_elim(lean_object* v_motive__1_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_Bool_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_81_, v_Bool_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Ite_elim___redArg(lean_object* v_t_85_, lean_object* v_Ite_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_85_, v_Ite_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Ite_elim(lean_object* v_motive__1_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_Ite_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_89_, v_Ite_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Int_elim___redArg(lean_object* v_t_93_, lean_object* v_Int_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_93_, v_Int_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Kind_Int_elim(lean_object* v_motive__1_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_Int_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lp_kanon__tiny__values_Tiny_Kind_ctorElim___redArg(v_t_97_, v_Int_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Term_kind(lean_object* v_x_101_){
_start:
{
lean_object* v_kind_102_; 
v_kind_102_ = lean_ctor_get(v_x_101_, 0);
lean_inc_ref(v_kind_102_);
return v_kind_102_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Term_kind___boxed(lean_object* v_x_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_kanon__tiny__values_Tiny_Term_kind(v_x_103_);
lean_dec_ref(v_x_103_);
return v_res_104_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Term_ty(lean_object* v_x_105_){
_start:
{
uint8_t v_ty_106_; 
v_ty_106_ = lean_ctor_get_uint8(v_x_105_, sizeof(void*)*1);
return v_ty_106_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Term_ty___boxed(lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = lp_kanon__tiny__values_Tiny_Term_ty(v_x_107_);
lean_dec_ref(v_x_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__0(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__0, &lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__0_once, _init_lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__0);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedKind(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1, &lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1_once, _init_lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1);
return v___x_114_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedTerm___closed__0(void){
_start:
{
uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = 0;
v___x_116_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1, &lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1_once, _init_lp_kanon__tiny__values_Tiny_instInhabitedKind___closed__1);
v___x_117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_instInhabitedTerm(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_instInhabitedTerm___closed__0, &lp_kanon__tiny__values_Tiny_instInhabitedTerm___closed__0_once, _init_lp_kanon__tiny__values_Tiny_instInhabitedTerm___closed__0);
return v___x_118_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Abstract(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Syntax(uint8_t builtin) {
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
res = initialize_kanon__tiny__values_Tiny_Abstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_kanon__tiny__values_Tiny_instInhabitedKind = _init_lp_kanon__tiny__values_Tiny_instInhabitedKind();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_instInhabitedKind);
lp_kanon__tiny__values_Tiny_instInhabitedTerm = _init_lp_kanon__tiny__values_Tiny_instInhabitedTerm();
lean_mark_persistent(lp_kanon__tiny__values_Tiny_instInhabitedTerm);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
