// Lean compiler output
// Module: Tiny.Semantics
// Imports: public import Init public meta import Init public import KanonCore.Sem public import KanonCore.BoolMod.Val public import Tiny.Model public import Tiny.Typing
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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_bool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_bool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_int_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_int_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqVal_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqVal_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqVal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Val_ty(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_intOp(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_kanon__tiny__values_Tiny_divOp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_kanon__tiny__values_Tiny_divOp___closed__0;
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_divOp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_zrem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_zrem___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_kanon__tiny__values_Tiny_Val_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
uint8_t v_b_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_b_8_ = lean_ctor_get_uint8(v_t_6_, 0);
lean_dec_ref_known(v_t_6_, 0);
v___x_9_ = lean_box(v_b_8_);
v___x_10_ = lean_apply_1(v_k_7_, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_z_11_; lean_object* v___x_12_; 
v_z_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_z_11_);
lean_dec_ref_known(v_t_6_, 1);
v___x_12_ = lean_apply_1(v_k_7_, v_z_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_kanon__tiny__values_Tiny_Val_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_bool_elim___redArg(lean_object* v_t_25_, lean_object* v_bool_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(v_t_25_, v_bool_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_bool_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_bool_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(v_t_29_, v_bool_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_int_elim___redArg(lean_object* v_t_33_, lean_object* v_int_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(v_t_33_, v_int_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_int_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_int_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_kanon__tiny__values_Tiny_Val_ctorElim___redArg(v_t_37_, v_int_39_);
return v___x_40_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqVal_decEq(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
if (lean_obj_tag(v_x_42_) == 0)
{
uint8_t v_b_43_; 
v_b_43_ = lean_ctor_get_uint8(v_x_41_, 0);
if (v_b_43_ == 0)
{
uint8_t v_b_44_; 
v_b_44_ = lean_ctor_get_uint8(v_x_42_, 0);
if (v_b_44_ == 0)
{
uint8_t v___x_45_; 
v___x_45_ = 1;
return v___x_45_;
}
else
{
return v_b_43_;
}
}
else
{
uint8_t v_b_46_; 
v_b_46_ = lean_ctor_get_uint8(v_x_42_, 0);
return v_b_46_;
}
}
else
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
}
else
{
if (lean_obj_tag(v_x_42_) == 0)
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
else
{
lean_object* v_z_49_; lean_object* v_z_50_; uint8_t v___x_51_; 
v_z_49_ = lean_ctor_get(v_x_41_, 0);
v_z_50_ = lean_ctor_get(v_x_42_, 0);
v___x_51_ = lean_int_dec_eq(v_z_49_, v_z_50_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqVal_decEq___boxed(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = lp_kanon__tiny__values_Tiny_instDecidableEqVal_decEq(v_x_52_, v_x_53_);
lean_dec_ref(v_x_53_);
lean_dec_ref(v_x_52_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_instDecidableEqVal(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lp_kanon__tiny__values_Tiny_instDecidableEqVal_decEq(v_x_56_, v_x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_instDecidableEqVal___boxed(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = lp_kanon__tiny__values_Tiny_instDecidableEqVal(v_x_59_, v_x_60_);
lean_dec_ref(v_x_60_);
lean_dec_ref(v_x_59_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t lp_kanon__tiny__values_Tiny_Val_ty(lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 1;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_Val_ty___boxed(lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = lp_kanon__tiny__values_Tiny_Val_ty(v_x_66_);
lean_dec_ref(v_x_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_intOp(lean_object* v_f_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
if (lean_obj_tag(v_x_70_) == 1)
{
lean_object* v_val_72_; 
v_val_72_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_val_72_);
lean_dec_ref_known(v_x_70_, 1);
if (lean_obj_tag(v_val_72_) == 1)
{
if (lean_obj_tag(v_x_71_) == 1)
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_84_; 
v_val_73_ = lean_ctor_get(v_x_71_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_84_ == 0)
{
v___x_75_ = v_x_71_;
v_isShared_76_ = v_isSharedCheck_84_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v_x_71_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_84_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
if (lean_obj_tag(v_val_73_) == 1)
{
lean_object* v_z_77_; lean_object* v_z_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v_z_77_ = lean_ctor_get(v_val_72_, 0);
lean_inc(v_z_77_);
lean_dec_ref_known(v_val_72_, 1);
v_z_78_ = lean_ctor_get(v_val_73_, 0);
lean_inc(v_z_78_);
lean_dec_ref_known(v_val_73_, 1);
v___x_79_ = lean_apply_2(v_f_69_, v_z_77_, v_z_78_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_79_);
v___x_81_ = v___x_75_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
else
{
lean_object* v___x_83_; 
lean_del_object(v___x_75_);
lean_dec(v_val_73_);
lean_dec_ref_known(v_val_72_, 1);
lean_dec_ref(v_f_69_);
v___x_83_ = lean_box(0);
return v___x_83_;
}
}
}
else
{
lean_object* v___x_85_; 
lean_dec_ref_known(v_val_72_, 1);
lean_dec(v_x_71_);
lean_dec_ref(v_f_69_);
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v_val_72_);
lean_dec(v_x_71_);
lean_dec_ref(v_f_69_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_x_71_);
lean_dec(v_x_70_);
lean_dec_ref(v_f_69_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
}
static lean_object* _init_lp_kanon__tiny__values_Tiny_divOp___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_nat_to_int(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_divOp(lean_object* v_f_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_91_) == 1)
{
lean_object* v_val_93_; 
v_val_93_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_val_93_);
lean_dec_ref_known(v_x_91_, 1);
if (lean_obj_tag(v_val_93_) == 1)
{
if (lean_obj_tag(v_x_92_) == 1)
{
lean_object* v_val_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_115_; 
v_val_94_ = lean_ctor_get(v_x_92_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_115_ == 0)
{
v___x_96_ = v_x_92_;
v_isShared_97_ = v_isSharedCheck_115_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_val_94_);
lean_dec(v_x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_115_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
if (lean_obj_tag(v_val_94_) == 1)
{
lean_object* v_z_98_; lean_object* v_z_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_113_; 
v_z_98_ = lean_ctor_get(v_val_93_, 0);
lean_inc(v_z_98_);
lean_dec_ref_known(v_val_93_, 1);
v_z_99_ = lean_ctor_get(v_val_94_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v_val_94_);
if (v_isSharedCheck_113_ == 0)
{
v___x_101_ = v_val_94_;
v_isShared_102_ = v_isSharedCheck_113_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_z_99_);
lean_dec(v_val_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_113_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_divOp___closed__0, &lp_kanon__tiny__values_Tiny_divOp___closed__0_once, _init_lp_kanon__tiny__values_Tiny_divOp___closed__0);
v___x_104_ = lean_int_dec_eq(v_z_99_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_105_ = lean_apply_2(v_f_90_, v_z_98_, v_z_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_105_);
v___x_107_ = v___x_101_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_111_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_107_);
v___x_109_ = v___x_96_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v___x_112_; 
lean_del_object(v___x_101_);
lean_dec(v_z_99_);
lean_dec(v_z_98_);
lean_del_object(v___x_96_);
lean_dec_ref(v_f_90_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
}
else
{
lean_object* v___x_114_; 
lean_del_object(v___x_96_);
lean_dec(v_val_94_);
lean_dec_ref_known(v_val_93_, 1);
lean_dec_ref(v_f_90_);
v___x_114_ = lean_box(0);
return v___x_114_;
}
}
}
else
{
lean_object* v___x_116_; 
lean_dec_ref_known(v_val_93_, 1);
lean_dec(v_x_92_);
lean_dec_ref(v_f_90_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
lean_dec(v_val_93_);
lean_dec(v_x_92_);
lean_dec_ref(v_f_90_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v_x_92_);
lean_dec(v_x_91_);
lean_dec_ref(v_f_90_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_zrem(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_obj_once(&lp_kanon__tiny__values_Tiny_divOp___closed__0, &lp_kanon__tiny__values_Tiny_divOp___closed__0_once, _init_lp_kanon__tiny__values_Tiny_divOp___closed__0);
v___x_122_ = lean_int_dec_le(v___x_121_, v_y_120_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_int_emod(v_x_119_, v_y_120_);
v___x_124_ = lean_int_neg(v___x_123_);
lean_dec(v___x_123_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_int_emod(v_x_119_, v_y_120_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* lp_kanon__tiny__values_Tiny_zrem___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = lp_kanon__tiny__values_Tiny_zrem(v_x_126_, v_y_127_);
lean_dec(v_y_127_);
lean_dec(v_x_126_);
return v_res_128_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_kanon_KanonCore_Sem(uint8_t builtin);
lean_object* initialize_kanon_KanonCore_BoolMod_Val(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Model(uint8_t builtin);
lean_object* initialize_kanon__tiny__values_Tiny_Typing(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_kanon__tiny__values_Tiny_Semantics(uint8_t builtin) {
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
res = initialize_kanon_KanonCore_Sem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_kanon_KanonCore_BoolMod_Val(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_kanon__tiny__values_Tiny_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_kanon__tiny__values_Tiny_Typing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
