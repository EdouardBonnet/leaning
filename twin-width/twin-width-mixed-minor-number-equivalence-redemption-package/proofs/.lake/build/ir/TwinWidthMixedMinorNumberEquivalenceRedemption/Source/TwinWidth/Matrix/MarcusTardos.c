// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MarcusTardos
// Imports: public import Init public meta import Init public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.GridMinor public import Mathlib.Algebra.Order.BigOperators.Group.Finset public import Mathlib.Data.Finset.Sort public import Mathlib.Logic.Equiv.Fin.Basic public import Mathlib.Order.Hom.Basic public import Mathlib.Order.Interval.Finset.Fin
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_fast__choose(lean_object*, lean_object*);
lean_object* lp_mathlib_finProdFinEquiv___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_prodComm(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_zeroBoolMatrix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_zeroBoolMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___lam__0___boxed(lean_object*);
static const lean_closure_object lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___closed__0 = (const lean_object*)&lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___closed__0_value;
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation___closed__0;
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_padToSquare(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_padToSquare___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPatternFurediHajnalConstant(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPatternFurediHajnalConstant___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_marcusTardosConstant(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_marcusTardosConstant___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___redArg(lean_object* v_00_u03c0_1_, lean_object* v_i_2_, lean_object* v_j_3_){
_start:
{
lean_object* v_toFun_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_toFun_4_ = lean_ctor_get(v_00_u03c0_1_, 0);
lean_inc(v_toFun_4_);
lean_dec_ref(v_00_u03c0_1_);
v___x_5_ = lean_apply_1(v_toFun_4_, v_i_2_);
v___x_6_ = lean_nat_dec_eq(v_j_3_, v___x_5_);
lean_dec(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___redArg___boxed(lean_object* v_00_u03c0_7_, lean_object* v_i_8_, lean_object* v_j_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___redArg(v_00_u03c0_7_, v_i_8_, v_j_9_);
lean_dec(v_j_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix(lean_object* v_k_12_, lean_object* v_00_u03c0_13_, lean_object* v_i_14_, lean_object* v_j_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___redArg(v_00_u03c0_13_, v_i_14_, v_j_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix___boxed(lean_object* v_k_17_, lean_object* v_00_u03c0_18_, lean_object* v_i_19_, lean_object* v_j_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_permutationMatrix(v_k_17_, v_00_u03c0_18_, v_i_19_, v_j_20_);
lean_dec(v_j_20_);
lean_dec(v_k_17_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_zeroBoolMatrix(lean_object* v_n_23_, lean_object* v_m_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_zeroBoolMatrix___boxed(lean_object* v_n_28_, lean_object* v_m_29_, lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_zeroBoolMatrix(v_n_28_, v_m_29_, v_x_30_, v_x_31_);
lean_dec(v_x_31_);
lean_dec(v_x_30_);
lean_dec(v_m_29_);
lean_dec(v_n_28_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___lam__0(lean_object* v___y_34_){
_start:
{
lean_inc(v___y_34_);
return v___y_34_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___lam__0___boxed(lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___lam__0(v___y_35_);
lean_dec(v___y_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb(lean_object* v_m_38_, lean_object* v_n_39_, lean_object* v_hmn_40_){
_start:
{
lean_object* v___f_41_; 
v___f_41_ = ((lean_object*)(lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___closed__0));
return v___f_41_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb___boxed(lean_object* v_m_42_, lean_object* v_n_43_, lean_object* v_hmn_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finCastLEOrderEmb(v_m_42_, v_n_43_, v_hmn_44_);
lean_dec(v_n_43_);
lean_dec(v_m_42_);
return v_res_45_;
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___redArg(lean_object* v_A_46_, lean_object* v_i_47_, lean_object* v_j_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_apply_2(v_A_46_, v_i_47_, v_j_48_);
v___x_50_ = lean_unbox(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___redArg___boxed(lean_object* v_A_51_, lean_object* v_i_52_, lean_object* v_j_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___redArg(v_A_51_, v_i_52_, v_j_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix(lean_object* v_m_56_, lean_object* v_n_57_, lean_object* v_hmn_58_, lean_object* v_A_59_, lean_object* v_i_60_, lean_object* v_j_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_apply_2(v_A_59_, v_i_60_, v_j_61_);
v___x_63_ = lean_unbox(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix___boxed(lean_object* v_m_64_, lean_object* v_n_65_, lean_object* v_hmn_66_, lean_object* v_A_67_, lean_object* v_i_68_, lean_object* v_j_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_cropMatrix(v_m_64_, v_n_65_, v_hmn_66_, v_A_67_, v_i_68_, v_j_69_);
lean_dec(v_n_65_);
lean_dec(v_m_64_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___redArg(lean_object* v_m_72_, lean_object* v_x_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_nat_dec_lt(v_x_73_, v_m_72_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
v___x_75_ = lean_unsigned_to_nat(0u);
return v___x_75_;
}
else
{
lean_inc(v_x_73_);
return v_x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___redArg___boxed(lean_object* v_m_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___redArg(v_m_76_, v_x_77_);
lean_dec(v_x_77_);
lean_dec(v_m_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict(lean_object* v_m_79_, lean_object* v_n_80_, lean_object* v_hm_81_, lean_object* v_x_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___redArg(v_m_79_, v_x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict___boxed(lean_object* v_m_84_, lean_object* v_n_85_, lean_object* v_hm_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_finRestrict(v_m_84_, v_n_85_, v_hm_86_, v_x_87_);
lean_dec(v_x_87_);
lean_dec(v_n_85_);
lean_dec(v_m_84_);
return v_res_88_;
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___lam__0(lean_object* v_I_89_, lean_object* v_s_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = lean_nat_mul(v_I_89_, v_s_90_);
v___x_93_ = lean_nat_dec_le(v___x_92_, v_a_91_);
lean_dec(v___x_92_);
if (v___x_93_ == 0)
{
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_I_89_, v___x_94_);
v___x_96_ = lean_nat_mul(v___x_95_, v_s_90_);
lean_dec(v___x_95_);
v___x_97_ = lean_nat_dec_lt(v_a_91_, v___x_96_);
lean_dec(v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___lam__0___boxed(lean_object* v_I_98_, lean_object* v_s_99_, lean_object* v_a_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___lam__0(v_I_98_, v_s_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec(v_s_99_);
lean_dec(v_I_98_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows(lean_object* v_q_103_, lean_object* v_s_104_, lean_object* v_I_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
lean_inc(v_s_104_);
v___f_106_ = lean_alloc_closure((void*)(lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___lam__0___boxed), 3, 2);
lean_closure_set(v___f_106_, 0, v_I_105_);
lean_closure_set(v___f_106_, 1, v_s_104_);
v___x_107_ = lean_nat_mul(v_q_103_, v_s_104_);
lean_dec(v_s_104_);
v___x_108_ = l_List_finRange(v___x_107_);
v___x_109_ = lp_mathlib_Multiset_filter___redArg(v___f_106_, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows___boxed(lean_object* v_q_110_, lean_object* v_s_111_, lean_object* v_I_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockRows(v_q_110_, v_s_111_, v_I_112_);
lean_dec(v_q_110_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___lam__0(lean_object* v_J_114_, lean_object* v_s_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_nat_mul(v_J_114_, v_s_115_);
v___x_118_ = lean_nat_dec_le(v___x_117_, v_a_116_);
lean_dec(v___x_117_);
if (v___x_118_ == 0)
{
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_J_114_, v___x_119_);
v___x_121_ = lean_nat_mul(v___x_120_, v_s_115_);
lean_dec(v___x_120_);
v___x_122_ = lean_nat_dec_lt(v_a_116_, v___x_121_);
lean_dec(v___x_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___lam__0___boxed(lean_object* v_J_123_, lean_object* v_s_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___lam__0(v_J_123_, v_s_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec(v_s_124_);
lean_dec(v_J_123_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols(lean_object* v_q_128_, lean_object* v_s_129_, lean_object* v_J_130_){
_start:
{
lean_object* v___f_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_inc(v_s_129_);
v___f_131_ = lean_alloc_closure((void*)(lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___lam__0___boxed), 3, 2);
lean_closure_set(v___f_131_, 0, v_J_130_);
lean_closure_set(v___f_131_, 1, v_s_129_);
v___x_132_ = lean_nat_mul(v_q_128_, v_s_129_);
lean_dec(v_s_129_);
v___x_133_ = l_List_finRange(v___x_132_);
v___x_134_ = lp_mathlib_Multiset_filter___redArg(v___f_131_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols___boxed(lean_object* v_q_135_, lean_object* v_s_136_, lean_object* v_J_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockCols(v_q_135_, v_s_136_, v_J_137_);
lean_dec(v_q_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___redArg(lean_object* v_s_139_, lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_nat_div(v_x_140_, v_s_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___redArg___boxed(lean_object* v_s_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___redArg(v_s_142_, v_x_143_);
lean_dec(v_x_143_);
lean_dec(v_s_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex(lean_object* v_q_145_, lean_object* v_s_146_, lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_nat_div(v_x_147_, v_s_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex___boxed(lean_object* v_q_149_, lean_object* v_s_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_blockIndex(v_q_149_, v_s_150_, v_x_151_);
lean_dec(v_x_151_);
lean_dec(v_s_150_);
lean_dec(v_q_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___redArg(lean_object* v_s_153_, lean_object* v_p_154_){
_start:
{
lean_object* v_fst_155_; lean_object* v_snd_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_165_; 
v_fst_155_ = lean_ctor_get(v_p_154_, 0);
v_snd_156_ = lean_ctor_get(v_p_154_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_p_154_);
if (v_isSharedCheck_165_ == 0)
{
v___x_158_ = v_p_154_;
v_isShared_159_ = v_isSharedCheck_165_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_snd_156_);
lean_inc(v_fst_155_);
lean_dec(v_p_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_165_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_160_ = lean_nat_div(v_fst_155_, v_s_153_);
lean_dec(v_fst_155_);
v___x_161_ = lean_nat_div(v_snd_156_, v_s_153_);
lean_dec(v_snd_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_161_);
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_163_ = v___x_158_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___redArg___boxed(lean_object* v_s_166_, lean_object* v_p_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___redArg(v_s_166_, v_p_167_);
lean_dec(v_s_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex(lean_object* v_q_169_, lean_object* v_s_170_, lean_object* v_p_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___redArg(v_s_170_, v_p_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex___boxed(lean_object* v_q_173_, lean_object* v_s_174_, lean_object* v_p_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_entryBlockIndex(v_q_173_, v_s_174_, v_p_175_);
lean_dec(v_s_174_);
lean_dec(v_q_173_);
return v_res_176_;
}
}
static lean_object* _init_lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation___closed__0(void){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lp_mathlib_Equiv_prodComm(lean_box(0), lean_box(0));
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation(lean_object* v_t_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_179_ = lp_mathlib_finProdFinEquiv___redArg(v_t_178_);
lean_inc_ref(v___x_179_);
v___x_180_ = lp_mathlib_Equiv_symm___redArg(v___x_179_);
v___x_181_ = lean_obj_once(&lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation___closed__0, &lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation___closed__0_once, _init_lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPermutation___closed__0);
v___x_182_ = lp_mathlib_Equiv_trans___redArg(v___x_180_, v___x_181_);
v___x_183_ = lp_mathlib_Equiv_trans___redArg(v___x_182_, v___x_179_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridIndex(lean_object* v_t_184_, lean_object* v_i_185_, lean_object* v_j_186_){
_start:
{
lean_object* v___x_187_; lean_object* v_toFun_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v___x_187_ = lp_mathlib_finProdFinEquiv___redArg(v_t_184_);
v_toFun_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v___x_187_, 1);
lean_dec(v_unused_197_);
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_toFun_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v_j_186_);
lean_ctor_set(v___x_190_, 0, v_i_185_);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_i_185_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_j_186_);
v___x_193_ = v_reuseFailAlloc_195_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_apply_1(v_toFun_188_, v___x_193_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT uint8_t lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_padToSquare(lean_object* v_n_198_, lean_object* v_m_199_, lean_object* v_M_200_, lean_object* v_r_201_, lean_object* v_c_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_nat_dec_lt(v_r_201_, v_n_198_);
if (v___x_203_ == 0)
{
lean_dec(v_c_202_);
lean_dec(v_r_201_);
lean_dec_ref(v_M_200_);
return v___x_203_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = lean_nat_dec_lt(v_c_202_, v_m_199_);
if (v___x_204_ == 0)
{
lean_dec(v_c_202_);
lean_dec(v_r_201_);
lean_dec_ref(v_M_200_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_apply_2(v_M_200_, v_r_201_, v_c_202_);
v___x_206_ = lean_unbox(v___x_205_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_padToSquare___boxed(lean_object* v_n_207_, lean_object* v_m_208_, lean_object* v_M_209_, lean_object* v_r_210_, lean_object* v_c_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_padToSquare(v_n_207_, v_m_208_, v_M_209_, v_r_210_, v_c_211_);
lean_dec(v_m_208_);
lean_dec(v_n_207_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPatternFurediHajnalConstant(lean_object* v_t_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_215_ = lean_unsigned_to_nat(2u);
v___x_216_ = lean_nat_mul(v_t_214_, v_t_214_);
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = lean_nat_pow(v___x_216_, v___x_217_);
v___x_219_ = lean_nat_mul(v___x_215_, v___x_218_);
lean_dec(v___x_218_);
v___x_220_ = lean_nat_pow(v___x_216_, v___x_215_);
v___x_221_ = lp_mathlib_Nat_fast__choose(v___x_220_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v___x_220_);
v___x_222_ = lean_nat_mul(v___x_219_, v___x_221_);
lean_dec(v___x_221_);
lean_dec(v___x_219_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPatternFurediHajnalConstant___boxed(lean_object* v_t_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPatternFurediHajnalConstant(v_t_223_);
lean_dec(v_t_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_marcusTardosConstant(lean_object* v_t_225_){
_start:
{
lean_object* v_zero_226_; uint8_t v_isZero_227_; 
v_zero_226_ = lean_unsigned_to_nat(0u);
v_isZero_227_ = lean_nat_dec_eq(v_t_225_, v_zero_226_);
if (v_isZero_227_ == 1)
{
return v_zero_226_;
}
else
{
lean_object* v_one_228_; lean_object* v_n_229_; uint8_t v_isZero_230_; 
v_one_228_ = lean_unsigned_to_nat(1u);
v_n_229_ = lean_nat_sub(v_t_225_, v_one_228_);
v_isZero_230_ = lean_nat_dec_eq(v_n_229_, v_zero_226_);
if (v_isZero_230_ == 1)
{
lean_dec(v_n_229_);
return v_one_228_;
}
else
{
lean_object* v_n_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_n_231_ = lean_nat_sub(v_n_229_, v_one_228_);
lean_dec(v_n_229_);
v___x_232_ = lean_unsigned_to_nat(2u);
v___x_233_ = lean_nat_add(v_n_231_, v___x_232_);
lean_dec(v_n_231_);
v___x_234_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_gridPatternFurediHajnalConstant(v___x_233_);
lean_dec(v___x_233_);
v___x_235_ = lean_nat_add(v___x_234_, v_one_228_);
lean_dec(v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_marcusTardosConstant___boxed(lean_object* v_t_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_marcusTardosConstant(v_t_236_);
lean_dec(v_t_236_);
return v_res_237_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_GridMinor(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Group_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Sort(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Equiv_Fin_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Hom_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Interval_Finset_Fin(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_MarcusTardos(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_GridMinor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Group_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Sort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Logic_Equiv_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Hom_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Interval_Finset_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
