// Lean compiler output
// Module: TwinWidthTreewidthExponentialRedemption.Statements.BonnetDepresBranch
// Imports: public import Init public meta import Init public import TwinWidthTreewidthExponentialRedemption.Statements.BonnetDepresApexCount
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
lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresApexCount_bonnetDepresApexCount(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresBranch_bonnetDepresBranch(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresBranch_bonnetDepresBranch___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresBranch_bonnetDepresBranch(lean_object* v_k_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_unsigned_to_nat(2u);
v___x_3_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresApexCount_bonnetDepresApexCount(v_k_1_);
v___x_4_ = lean_nat_pow(v___x_2_, v___x_3_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresBranch_bonnetDepresBranch___boxed(lean_object* v_k_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresBranch_bonnetDepresBranch(v_k_5_);
lean_dec(v_k_5_);
return v_res_6_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresApexCount(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresBranch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_BonnetDepresApexCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
