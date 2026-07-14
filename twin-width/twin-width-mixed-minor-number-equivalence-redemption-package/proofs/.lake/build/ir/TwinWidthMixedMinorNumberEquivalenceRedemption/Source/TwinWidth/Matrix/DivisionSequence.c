// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.DivisionSequence
// Imports: public import Init public meta import Init public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Fusion public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MarcusTardos public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.TwinWidth
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_lemma13MixedValueBound(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___redArg(lean_object* v_D_1_){
_start:
{
lean_object* v_rowCuts_2_; lean_object* v_colCuts_3_; lean_object* v___x_4_; 
v_rowCuts_2_ = lean_ctor_get(v_D_1_, 0);
v_colCuts_3_ = lean_ctor_get(v_D_1_, 1);
v___x_4_ = lean_nat_add(v_rowCuts_2_, v_colCuts_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___redArg___boxed(lean_object* v_D_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___redArg(v_D_5_);
lean_dec_ref(v_D_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount(lean_object* v_n_7_, lean_object* v_m_8_, lean_object* v_D_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___redArg(v_D_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount___boxed(lean_object* v_n_11_, lean_object* v_m_12_, lean_object* v_D_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MatrixDivision_cutCount(v_n_11_, v_m_12_, v_D_13_);
lean_dec_ref(v_D_13_);
lean_dec(v_m_12_);
lean_dec(v_n_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg___lam__0(lean_object* v_D_15_, lean_object* v_division_16_, lean_object* v_s_17_){
_start:
{
lean_object* v_zero_18_; uint8_t v_isZero_19_; 
v_zero_18_ = lean_unsigned_to_nat(0u);
v_isZero_19_ = lean_nat_dec_eq(v_s_17_, v_zero_18_);
if (v_isZero_19_ == 1)
{
lean_dec_ref(v_division_16_);
lean_inc_ref(v_D_15_);
return v_D_15_;
}
else
{
lean_object* v_one_20_; lean_object* v_n_21_; lean_object* v___x_22_; 
v_one_20_ = lean_unsigned_to_nat(1u);
v_n_21_ = lean_nat_sub(v_s_17_, v_one_20_);
v___x_22_ = lean_apply_1(v_division_16_, v_n_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg___lam__0___boxed(lean_object* v_D_23_, lean_object* v_division_24_, lean_object* v_s_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg___lam__0(v_D_23_, v_division_24_, v_s_25_);
lean_dec(v_s_25_);
lean_dec_ref(v_D_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg(lean_object* v_D_27_, lean_object* v_S_28_){
_start:
{
lean_object* v_stepCount_29_; lean_object* v_division_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_40_; 
v_stepCount_29_ = lean_ctor_get(v_S_28_, 0);
v_division_30_ = lean_ctor_get(v_S_28_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v_S_28_);
if (v_isSharedCheck_40_ == 0)
{
v___x_32_ = v_S_28_;
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_division_30_);
lean_inc(v_stepCount_29_);
lean_dec(v_S_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_40_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___f_34_ = lean_alloc_closure((void*)(lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_34_, 0, v_D_27_);
lean_closure_set(v___f_34_, 1, v_division_30_);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_stepCount_29_, v___x_35_);
lean_dec(v_stepCount_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 1, v___f_34_);
lean_ctor_set(v___x_32_, 0, v___x_36_);
v___x_38_ = v___x_32_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v___f_34_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons(lean_object* v_00_u03b1_41_, lean_object* v_n_42_, lean_object* v_m_43_, lean_object* v_d_44_, lean_object* v_M_45_, lean_object* v_D_46_, lean_object* v_E_47_, lean_object* v_hDE_48_, lean_object* v_hD_49_, lean_object* v_S_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___redArg(v_D_46_, v_S_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons___boxed(lean_object* v_00_u03b1_52_, lean_object* v_n_53_, lean_object* v_m_54_, lean_object* v_d_55_, lean_object* v_M_56_, lean_object* v_D_57_, lean_object* v_E_58_, lean_object* v_hDE_59_, lean_object* v_hD_60_, lean_object* v_S_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_BoundedMixedValueDivisionTail_cons(v_00_u03b1_52_, v_n_53_, v_m_54_, v_d_55_, v_M_56_, v_D_57_, v_E_58_, v_hDE_59_, v_hD_60_, v_S_61_);
lean_dec_ref(v_E_58_);
lean_dec(v_M_56_);
lean_dec(v_d_55_);
lean_dec(v_m_54_);
lean_dec(v_n_53_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail___redArg(lean_object* v_S_63_){
_start:
{
lean_object* v_stepCount_64_; lean_object* v_division_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_stepCount_64_ = lean_ctor_get(v_S_63_, 0);
v_division_65_ = lean_ctor_get(v_S_63_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_S_63_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v_S_63_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_division_65_);
lean_inc(v_stepCount_64_);
lean_dec(v_S_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_stepCount_64_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_division_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail(lean_object* v_00_u03b1_73_, lean_object* v_n_74_, lean_object* v_m_75_, lean_object* v_d_76_, lean_object* v_M_77_, lean_object* v_D_u2080_78_, lean_object* v_hfinest_79_, lean_object* v_S_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail___redArg(v_S_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail___boxed(lean_object* v_00_u03b1_82_, lean_object* v_n_83_, lean_object* v_m_84_, lean_object* v_d_85_, lean_object* v_M_86_, lean_object* v_D_u2080_87_, lean_object* v_hfinest_88_, lean_object* v_S_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_boundedMixedValueDivisionSequence__of__tail(v_00_u03b1_82_, v_n_83_, v_m_84_, v_d_85_, v_M_86_, v_D_u2080_87_, v_hfinest_88_, v_S_89_);
lean_dec_ref(v_D_u2080_87_);
lean_dec(v_M_86_);
lean_dec(v_d_85_);
lean_dec(v_m_84_);
lean_dec(v_n_83_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_lemma13MixedValueBound(lean_object* v_c_91_, lean_object* v_t_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(20u);
v___x_94_ = lean_apply_1(v_c_91_, v_t_92_);
v___x_95_ = lean_nat_mul(v___x_93_, v___x_94_);
lean_dec(v___x_94_);
return v___x_95_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MarcusTardos(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_TwinWidth(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_DivisionSequence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Fusion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MarcusTardos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_TwinWidth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
