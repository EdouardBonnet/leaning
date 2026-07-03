// Lean compiler output
// Module: TwinWidthTreewidthExponentialRedemption.Proofs.Main
// Imports: public import Init public meta import Init public import TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.BonnetDepresLower public import TwinWidthTreewidthExponentialRedemption.Statements.Main
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
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___redArg(lean_object* v_bags_1_){
_start:
{
lean_inc(v_bags_1_);
return v_bags_1_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___redArg___boxed(lean_object* v_bags_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___redArg(v_bags_2_);
lean_dec(v_bags_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted(lean_object* v_V_4_, lean_object* v_inst_5_, lean_object* v_bags_6_, lean_object* v_blackAdj_7_, lean_object* v_redAdj_8_, lean_object* v_h_9_){
_start:
{
lean_inc(v_bags_6_);
return v_bags_6_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted___boxed(lean_object* v_V_10_, lean_object* v_inst_11_, lean_object* v_bags_12_, lean_object* v_blackAdj_13_, lean_object* v_redAdj_14_, lean_object* v_h_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main_sourceTrigraphStateOfSubmitted(v_V_10_, v_inst_11_, v_bags_12_, v_blackAdj_13_, v_redAdj_14_, v_h_15_);
lean_dec(v_bags_12_);
lean_dec_ref(v_inst_11_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Statements_Source_TwinWidth_Graph_BonnetDepresLower(uint8_t builtin);
lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Proofs_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthTreewidthExponentialRedemption_x2eProofs_TwinWidthTreewidthExponentialRedemption_Statements_Source_TwinWidth_Graph_BonnetDepresLower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
