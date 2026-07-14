// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Contraction.TwinWidth
// Imports: public import Init public meta import Init public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Contraction.Trigraph
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
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_List_decidablePerm___redArg(v_inst_1_, v_a_2_, v_b_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg___lam__0___boxed(lean_object* v_inst_5_, lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg___lam__0(v_inst_5_, v_a_6_, v_b_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg(lean_object* v_inst_10_, lean_object* v_A_11_, lean_object* v_B_12_, lean_object* v_X_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
lean_inc(v_B_12_);
lean_inc(v_A_11_);
lean_inc_ref_n(v_inst_10_, 2);
v___x_14_ = lp_mathlib_Multiset_ndunion___redArg(v_inst_10_, v_A_11_, v_B_12_);
lean_inc(v_X_13_);
v___x_15_ = l_List_decidablePerm___redArg(v_inst_10_, v_X_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_B_12_);
lean_dec(v_A_11_);
lean_dec_ref(v_inst_10_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v_X_13_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
return v___x_17_;
}
else
{
lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_X_13_);
v___f_18_ = lean_alloc_closure((void*)(lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_18_, 0, v_inst_10_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_20_, 0, v_B_12_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
v___x_21_ = lp_mathlib_Multiset_ndinsert___redArg(v___f_18_, v_A_11_, v___x_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages(lean_object* v_V_22_, lean_object* v_inst_23_, lean_object* v_A_24_, lean_object* v_B_25_, lean_object* v_X_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_contractionPreimages___redArg(v_inst_23_, v_A_24_, v_B_25_, v_X_26_);
return v___x_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Contraction_Trigraph(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Contraction_TwinWidth(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Contraction_Trigraph(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
