// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Fusion
// Imports: public import Init public meta import Init public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Corner
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
lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Division_fuseIndex___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage___redArg(lean_object* v_i_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_val_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_val_3_ = lean_ctor_get(v_x_2_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_x_2_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_val_3_);
lean_dec(v_x_2_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Division_fuseIndex___redArg(v_i_1_, v_val_3_);
lean_dec(v_val_3_);
lean_dec(v_i_1_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_val_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_29_; 
v_val_12_ = lean_ctor_get(v_x_2_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_29_ == 0)
{
v___x_14_ = v_x_2_;
v_isShared_15_ = v_isSharedCheck_29_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_val_12_);
lean_dec(v_x_2_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_29_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_lt(v_val_12_, v_i_1_);
if (v___x_16_ == 0)
{
uint8_t v___x_17_; 
v___x_17_ = lean_nat_dec_eq(v_val_12_, v_i_1_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
lean_dec(v_i_1_);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_sub(v_val_12_, v___x_18_);
lean_dec(v_val_12_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_19_);
v___x_21_ = v___x_14_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v___x_24_; 
lean_dec(v_val_12_);
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 0);
lean_ctor_set(v___x_14_, 0, v_i_1_);
v___x_24_ = v___x_14_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_i_1_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_object* v___x_27_; 
lean_dec(v_i_1_);
if (v_isShared_15_ == 0)
{
v___x_27_ = v___x_14_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_12_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage(lean_object* v_k_30_, lean_object* v_i_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage___redArg(v_i_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage___boxed(lean_object* v_k_34_, lean_object* v_i_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage(v_k_34_, v_i_35_, v_x_36_);
lean_dec(v_k_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter___redArg(lean_object* v_x_38_, lean_object* v_h__1_39_, lean_object* v_h__2_40_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v_val_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_40_);
v_val_41_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_val_41_);
lean_dec_ref(v_x_38_);
v___x_42_ = lean_apply_1(v_h__1_39_, v_val_41_);
return v___x_42_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_39_);
v_val_43_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_val_43_);
lean_dec_ref(v_x_38_);
v___x_44_ = lean_apply_1(v_h__2_40_, v_val_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter(lean_object* v_k_45_, lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_49_);
v_val_50_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_x_47_);
v___x_51_ = lean_apply_1(v_h__1_48_, v_val_50_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_48_);
v_val_52_ = lean_ctor_get(v_x_47_, 0);
lean_inc(v_val_52_);
lean_dec_ref(v_x_47_);
v___x_53_ = lean_apply_1(v_h__2_49_, v_val_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter___boxed(lean_object* v_k_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_rowFuseItemPreimage_match__1_splitter(v_k_54_, v_motive_55_, v_x_56_, v_h__1_57_, v_h__2_58_);
lean_dec(v_k_54_);
return v_res_59_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Corner(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Corner(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
