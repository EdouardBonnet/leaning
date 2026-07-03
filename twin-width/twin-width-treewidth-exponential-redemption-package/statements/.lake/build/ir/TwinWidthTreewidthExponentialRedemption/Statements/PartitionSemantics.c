// Lean compiler output
// Module: TwinWidthTreewidthExponentialRedemption.Statements.PartitionSemantics
// Imports: public import Init public meta import Init public import Mathlib.Combinatorics.SimpleGraph.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___closed__0 = (const lean_object*)&lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_A_2_, lean_object* v_B_3_, lean_object* v_X_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
lean_inc(v_B_3_);
lean_inc(v_A_2_);
lean_inc_ref(v_inst_1_);
v___x_5_ = lp_mathlib_Multiset_ndunion___redArg(v_inst_1_, v_A_2_, v_B_3_);
lean_inc(v_X_4_);
v___x_6_ = l_List_decidablePerm___redArg(v_inst_1_, v_X_4_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec(v_B_3_);
lean_dec(v_A_2_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_8_, 0, v_X_4_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_X_4_);
v___x_9_ = lean_box(0);
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v_B_3_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
v___x_11_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_11_, 0, v_A_2_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg(lean_object* v_inst_14_, lean_object* v_A_15_, lean_object* v_B_16_, lean_object* v_L_17_){
_start:
{
lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___f_18_ = lean_alloc_closure((void*)(lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___lam__0), 4, 3);
lean_closure_set(v___f_18_, 0, v_inst_14_);
lean_closure_set(v___f_18_, 1, v_A_15_);
lean_closure_set(v___f_18_, 2, v_B_16_);
v___x_19_ = ((lean_object*)(lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg___closed__0));
v___x_20_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___f_18_, v_L_17_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag(lean_object* v_V_21_, lean_object* v_inst_22_, lean_object* v_A_23_, lean_object* v_B_24_, lean_object* v_L_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics_splitMergedBag___redArg(v_inst_22_, v_A_23_, v_B_24_, v_L_25_);
return v___x_26_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthTreewidthExponentialRedemption_x2eStatements_TwinWidthTreewidthExponentialRedemption_Statements_PartitionSemantics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
