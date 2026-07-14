// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.IntervalDivision
// Imports: public import Init public meta import Init public import Mathlib.Data.Finset.Basic
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
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part___redArg(lean_object* v_D_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_D_1_, v_a_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part(lean_object* v_n_4_, lean_object* v_k_5_, lean_object* v_D_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_D_6_, v_a_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part___boxed(lean_object* v_n_9_, lean_object* v_k_10_, lean_object* v_D_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision_part(v_n_9_, v_k_10_, v_D_11_, v_a_12_);
lean_dec(v_k_10_);
lean_dec(v_n_9_);
return v_res_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eStatements_TwinWidthMixedMinorNumberEquivalenceRedemption_Statements_IntervalDivision(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
