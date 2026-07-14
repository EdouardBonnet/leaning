// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.TwinDecomposition
// Imports: public import Init public meta import Init public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.Theorem14 public import Mathlib.Data.List.NodupEquivFin
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_x_1_, v_one_8_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___redArg___boxed(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___redArg(v_x_11_, v_h__1_12_, v_h__2_13_);
lean_dec(v_x_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter(lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_zero_19_; uint8_t v_isZero_20_; 
v_zero_19_ = lean_unsigned_to_nat(0u);
v_isZero_20_ = lean_nat_dec_eq(v_x_16_, v_zero_19_);
if (v_isZero_20_ == 1)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_17_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_17_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_x_16_, v_one_23_);
v___x_25_ = lean_apply_1(v_h__2_18_, v_n_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter___boxed(lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_reverseBagList_match__1_splitter(v_motive_26_, v_x_27_, v_h__1_28_, v_h__2_29_);
lean_dec(v_x_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___redArg(lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_zero_34_; uint8_t v_isZero_35_; 
v_zero_34_ = lean_unsigned_to_nat(0u);
v_isZero_35_ = lean_nat_dec_eq(v_x_31_, v_zero_34_);
if (v_isZero_35_ == 1)
{
lean_object* v___x_36_; 
lean_dec(v_h__2_33_);
v___x_36_ = lean_apply_1(v_h__1_32_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v_one_37_; lean_object* v_n_38_; lean_object* v___x_39_; 
lean_dec(v_h__1_32_);
v_one_37_ = lean_unsigned_to_nat(1u);
v_n_38_ = lean_nat_sub(v_x_31_, v_one_37_);
v___x_39_ = lean_apply_2(v_h__2_33_, v_n_38_, lean_box(0));
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___redArg___boxed(lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___redArg(v_x_40_, v_h__1_41_, v_h__2_42_);
lean_dec(v_x_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter(lean_object* v_V_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_G_47_, lean_object* v_d_48_, lean_object* v_S_49_, lean_object* v_motive_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
lean_object* v_zero_55_; uint8_t v_isZero_56_; 
v_zero_55_ = lean_unsigned_to_nat(0u);
v_isZero_56_ = lean_nat_dec_eq(v_x_51_, v_zero_55_);
if (v_isZero_56_ == 1)
{
lean_object* v___x_57_; 
lean_dec(v_h__2_54_);
v___x_57_ = lean_apply_1(v_h__1_53_, lean_box(0));
return v___x_57_;
}
else
{
lean_object* v_one_58_; lean_object* v_n_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_53_);
v_one_58_ = lean_unsigned_to_nat(1u);
v_n_59_ = lean_nat_sub(v_x_51_, v_one_58_);
v___x_60_ = lean_apply_2(v_h__2_54_, v_n_59_, lean_box(0));
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter___boxed(lean_object* v_V_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_G_64_, lean_object* v_d_65_, lean_object* v_S_66_, lean_object* v_motive_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs___private_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition_0__TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_ContractionSequence_bagListDivisionAt_match__1_splitter(v_V_61_, v_inst_62_, v_inst_63_, v_G_64_, v_d_65_, v_S_66_, v_motive_67_, v_x_68_, v_x_69_, v_h__1_70_, v_h__2_71_);
lean_dec(v_x_68_);
lean_dec_ref(v_S_66_);
lean_dec(v_d_65_);
lean_dec_ref(v_inst_63_);
lean_dec(v_inst_62_);
return v_res_72_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_Theorem14(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_List_NodupEquivFin(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_TwinDecomposition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_Theorem14(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_List_NodupEquivFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
