// Lean compiler output
// Module: TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.Theorem14
// Imports: public import Init public meta import Init public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.Partition public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.MixedMinorNumber public import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Symmetric
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
lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_symmetricMatrixTwinWidthBoundOfMixedFree(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_theorem14MixedFreeTwinWidthBound(lean_object*);
LEAN_EXPORT lean_object* lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_SimpleGraph_theorem14MixedFreeTwinWidthBound(lean_object* v_t_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lp_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_symmetricMatrixTwinWidthBoundOfMixedFree(v_t_1_);
return v___x_2_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_Partition(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_MixedMinorNumber(uint8_t builtin);
lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Symmetric(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_Theorem14(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_Partition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Graph_MixedMinorNumber(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TwinWidthMixedMinorNumberEquivalenceRedemption_x2eProofs_TwinWidthMixedMinorNumberEquivalenceRedemption_Source_TwinWidth_Matrix_Symmetric(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
