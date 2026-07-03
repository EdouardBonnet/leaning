// Lean compiler output
// Module: TwinWidthTreewidthExponentialRedemption.Statements.FullTreeNodeParent
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
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___redArg___lam__0(lean_object* v_snd_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_snd_1_, v_i_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___redArg(lean_object* v_u_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_16_; 
v_fst_5_ = lean_ctor_get(v_u_4_, 0);
v_snd_6_ = lean_ctor_get(v_u_4_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_u_4_);
if (v_isSharedCheck_16_ == 0)
{
v___x_8_ = v_u_4_;
v_isShared_9_ = v_isSharedCheck_16_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
lean_dec(v_u_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_16_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___f_11_ = lean_alloc_closure((void*)(lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_snd_6_);
v___x_12_ = lean_nat_sub(v_fst_5_, v___x_10_);
lean_dec(v_fst_5_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___f_11_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_14_ = v___x_8_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___f_11_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent(lean_object* v_branch_17_, lean_object* v_depth_18_, lean_object* v_u_19_, lean_object* v_hlevel_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___redArg(v_u_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent___boxed(lean_object* v_branch_22_, lean_object* v_depth_23_, lean_object* v_u_24_, lean_object* v_hlevel_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent_fullTreeNodeParent(v_branch_22_, v_depth_23_, v_u_24_, v_hlevel_25_);
lean_dec(v_depth_23_);
lean_dec(v_branch_22_);
return v_res_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNode(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_FullTreeNodeParent(uint8_t builtin) {
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
