// Lean compiler output
// Module: TwinWidthTreewidthExponentialRedemption.Statements.FullTreeNodeLastLabel
// Imports: public import Init public meta import Init public import TwinWidthTreewidthExponentialRedemption.Statements.FullTreeNode
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel___redArg(lean_object* v_u_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_fst_2_ = lean_ctor_get(v_u_1_, 0);
lean_inc(v_fst_2_);
v_snd_3_ = lean_ctor_get(v_u_1_, 1);
lean_inc(v_snd_3_);
lean_dec_ref(v_u_1_);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_fst_2_, v___x_4_);
lean_dec(v_fst_2_);
v___x_6_ = lean_apply_1(v_snd_3_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel(lean_object* v_branch_7_, lean_object* v_depth_8_, lean_object* v_u_9_, lean_object* v_hlevel_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel___redArg(v_u_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel___boxed(lean_object* v_branch_12_, lean_object* v_depth_13_, lean_object* v_u_14_, lean_object* v_hlevel_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel_fullTreeNodeLastLabel(v_branch_12_, v_depth_13_, v_u_14_, v_hlevel_15_);
lean_dec(v_depth_13_);
lean_dec(v_branch_12_);
return v_res_16_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNode(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeLastLabel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
