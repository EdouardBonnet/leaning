import Chapter02.cycle_packing_reduction_aux
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

/-- Diestel uses logarithms to base two in Lemma 2.3.1. -/
noncomputable def logTwo (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

lemma logTwo_eq_logb (x : ℝ) : logTwo x = Real.logb 2 x := rfl

lemma logTwo_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    logTwo x ≤ logTwo y := by
  have hy : 0 < y := hx.trans_le hxy
  simpa [logTwo_eq_logb] using
    (Real.logb_le_logb (b := 2) (x := x) (y := y)
      (by norm_num) hx hy).2 hxy

lemma logTwo_strictMono {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    logTwo x < logTwo y := by
  simpa [logTwo_eq_logb] using
    Real.logb_lt_logb (b := 2) (x := x) (y := y)
      (by norm_num) hx hxy

lemma logTwo_two : logTwo 2 = 1 := by
  simpa [logTwo_eq_logb] using
    (Real.logb_self_eq_one (b := 2) (by norm_num))

lemma logTwo_one : logTwo 1 = 0 := by
  simp [logTwo]

lemma logTwo_four : logTwo 4 = 2 := by
  calc
    logTwo 4 = Real.logb 2 ((2 : ℝ) ^ 2) := by norm_num [logTwo_eq_logb]
    _ = (2 : ℝ) * Real.logb 2 2 := Real.logb_pow 2 2 2
    _ = 2 := by simp [Real.logb_self_eq_one (b := 2) (by norm_num)]

lemma logTwo_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logTwo (x * y) = logTwo x + logTwo y := by
  simpa [logTwo_eq_logb] using
    Real.logb_mul (b := 2) (x := x) (y := y) hx hy

lemma logTwo_lt_of_lt_two_pow_nat {x : ℝ} {n : ℕ}
    (hx : 0 < x) (hxn : x < (2 : ℝ) ^ n) :
    logTwo x < (n : ℝ) := by
  rw [logTwo_eq_logb]
  rw [Real.logb_lt_iff_lt_rpow (b := 2) (x := x) (y := (n : ℝ))
    (by norm_num) hx]
  simpa using hxn

lemma logTwo_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    logTwo x ≤ x := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcoeff : 1 ≤ Real.exp 1 * Real.log 2 := by
    have hexp : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      norm_num at h ⊢
      exact h
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith
  have hstep₁ :
      Real.log x ≤ (Real.exp 1 * Real.log 2) * Real.log x := by
    nlinarith
  have hstep₂ :
      (Real.exp 1 * Real.log 2) * Real.log x ≤ Real.log 2 * x := by
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have hexp_log :
        Real.exp 1 * Real.log x ≤ x := by
      simpa [Real.exp_log hxpos] using Real.exp_one_mul_le_exp (x := Real.log x)
    nlinarith
  have hlog_le : Real.log x ≤ Real.log 2 * x := hstep₁.trans hstep₂
  unfold logTwo
  rw [div_le_iff₀ hlog2pos]
  nlinarith

lemma logTwo_pos_of_one_lt {x : ℝ} (hx : 1 < x) :
    0 < logTwo x := by
  simpa [logTwo_one] using
    logTwo_strictMono (x := 1) (y := x) zero_lt_one hx

lemma two_le_logTwo_nat_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    (2 : ℝ) ≤ logTwo (k : ℝ) := by
  have hk_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h := logTwo_mono (x := 4) (y := (k : ℝ)) (by norm_num) hk_real
  simpa [logTwo_four] using h

lemma logTwo_nat_pos_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    0 < logTwo (k : ℝ) := by
  have hk_real : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  exact logTwo_pos_of_one_lt hk_real

lemma four_le_six_mul_log_two : (4 : ℝ) ≤ 6 * Real.log 2 := by
  have h := Real.log_two_gt_d9
  nlinarith

lemma four_mul_logTwo_sub_le_sub_of_six_le {a b : ℝ}
    (ha : 6 ≤ a) (hab : a ≤ b) :
    4 * (logTwo b - logTwo a) ≤ b - a := by
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hapos : 0 < a := by nlinarith
  have hbpos : 0 < b := hapos.trans_le hab
  have hratio_pos : 0 < b / a := div_pos hbpos hapos
  have hlog_le : Real.log b - Real.log a ≤ b / a - 1 := by
    have h := Real.log_le_sub_one_of_pos hratio_pos
    rw [Real.log_div hbpos.ne' hapos.ne'] at h
    exact h
  have hcoeff_nonneg : 0 ≤ 4 / Real.log 2 := by positivity
  have hmul :
      (4 / Real.log 2) * (Real.log b - Real.log a) ≤
        (4 / Real.log 2) * (b / a - 1) :=
    mul_le_mul_of_nonneg_left hlog_le hcoeff_nonneg
  have hcoeff_le : 4 / (a * Real.log 2) ≤ 1 := by
    rw [div_le_one]
    · nlinarith [four_le_six_mul_log_two, ha, hlog2pos]
    · positivity
  have hsub_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmul2 : (4 / (a * Real.log 2)) * (b - a) ≤ 1 * (b - a) :=
    mul_le_mul_of_nonneg_right hcoeff_le hsub_nonneg
  calc
    4 * (logTwo b - logTwo a)
        = (4 / Real.log 2) * (Real.log b - Real.log a) := by
          unfold logTwo
          ring
    _ ≤ (4 / Real.log 2) * (b / a - 1) := hmul
    _ = (4 / (a * Real.log 2)) * (b - a) := by
          field_simp [hapos.ne', hlog2pos.ne']
    _ ≤ 1 * (b - a) := hmul2
    _ = b - a := by ring

lemma sub_four_logTwo_mono_on_six {a b : ℝ}
    (ha : 6 ≤ a) (hab : a ≤ b) :
    a - 4 * logTwo a ≤ b - 4 * logTwo b := by
  have h := four_mul_logTwo_sub_le_sub_of_six_le (a := a) (b := b) ha hab
  linarith

lemma erdosPosaS_nonneg (k : ℕ) : 0 ≤ erdosPosaS k := by
  by_cases hk : 2 ≤ k
  · have hk_real_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hr_nonneg : 0 ≤ erdosPosaR k := by
      have h5 : (5 : ℝ) ≤ erdosPosaR k := five_le_erdosPosaR hk
      nlinarith
    simp [erdosPosaS, hk, mul_nonneg, hk_real_nonneg, hr_nonneg]
  · simp [erdosPosaS, hk]

lemma erdosPosaR_le_four_logTwo_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    erdosPosaR k ≤ 4 * logTwo (k : ℝ) := by
  have hL2 : (2 : ℝ) ≤ logTwo (k : ℝ) :=
    two_le_logTwo_nat_of_four_le hk
  have hlogL :
      logTwo (logTwo (k : ℝ)) ≤ logTwo (k : ℝ) :=
    logTwo_le_self_of_one_le (by linarith)
  change logTwo (k : ℝ) + logTwo (logTwo (k : ℝ)) + 4 ≤
    4 * logTwo (k : ℝ)
  nlinarith

lemma erdosPosaR_pred_lt_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    erdosPosaR (k - 1) < erdosPosaR k := by
  have hkpred2 : 2 ≤ k - 1 := by omega
  have hkpred_pos : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hpred_lt : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by
    exact_mod_cast (by omega : k - 1 < k)
  have hLlt :
      logTwo ((k - 1 : ℕ) : ℝ) < logTwo (k : ℝ) :=
    logTwo_strictMono hkpred_pos hpred_lt
  have hLpred_pos : 0 < logTwo ((k - 1 : ℕ) : ℝ) :=
    logTwo_nat_pos_of_two_le hkpred2
  have hlogLle :
      logTwo (logTwo ((k - 1 : ℕ) : ℝ)) ≤
        logTwo (logTwo (k : ℝ)) :=
    logTwo_mono hLpred_pos hLlt.le
  change
    logTwo ((k - 1 : ℕ) : ℝ) +
        logTwo (logTwo ((k - 1 : ℕ) : ℝ)) + 4 <
      logTwo (k : ℝ) + logTwo (logTwo (k : ℝ)) + 4
  nlinarith

lemma logTwo_erdosPosaS_le_erdosPosaR_of_four_le {k : ℕ}
    (hk : 4 ≤ k) :
    logTwo (erdosPosaS k) ≤ erdosPosaR k := by
  have hk2 : 2 ≤ k := by omega
  have hkpos : ((k : ℝ) ≠ 0) := by
    exact_mod_cast (by omega : k ≠ 0)
  have hRpos : 0 < erdosPosaR k := by
    have h5 : (5 : ℝ) ≤ erdosPosaR k := five_le_erdosPosaR hk2
    nlinarith
  have hRle : erdosPosaR k ≤ 4 * logTwo (k : ℝ) :=
    erdosPosaR_le_four_logTwo_of_four_le hk
  have hLpos : 0 < logTwo (k : ℝ) :=
    logTwo_nat_pos_of_two_le hk2
  have hlogRle :
      logTwo (erdosPosaR k) ≤ logTwo (4 * logTwo (k : ℝ)) :=
    logTwo_mono hRpos hRle
  have hlog4L :
      logTwo (4 * logTwo (k : ℝ)) =
        2 + logTwo (logTwo (k : ℝ)) := by
    rw [logTwo_mul (by norm_num) (ne_of_gt hLpos)]
    simp [logTwo_four, add_comm, add_left_comm, add_assoc]
  have hlogR :
      logTwo (erdosPosaR k) ≤
        2 + logTwo (logTwo (k : ℝ)) := by
    simpa [hlog4L] using hlogRle
  have hS :
      logTwo (erdosPosaS k) =
        2 + logTwo (k : ℝ) + logTwo (erdosPosaR k) := by
    rw [erdosPosaS, if_pos hk2]
    calc
      logTwo (4 * (k : ℝ) * erdosPosaR k)
          = logTwo (4 * (k : ℝ)) + logTwo (erdosPosaR k) := by
            rw [logTwo_mul (mul_ne_zero (by norm_num) hkpos) (ne_of_gt hRpos)]
      _ = (logTwo 4 + logTwo (k : ℝ)) + logTwo (erdosPosaR k) := by
            rw [logTwo_mul (by norm_num) hkpos]
      _ = 2 + logTwo (k : ℝ) + logTwo (erdosPosaR k) := by
            simp [logTwo_four, add_comm, add_left_comm, add_assoc]
  rw [hS]
  change
    2 + logTwo (k : ℝ) + logTwo (erdosPosaR k) ≤
      logTwo (k : ℝ) + logTwo (logTwo (k : ℝ)) + 4
  nlinarith

lemma erdosPosaS_pred_lt_sub_four_logTwo_of_four_le {k : ℕ}
    (hk : 4 ≤ k) :
    erdosPosaS (k - 1) <
      erdosPosaS k - 4 * logTwo (erdosPosaS k) := by
  have hk2 : 2 ≤ k := by omega
  have hkpred2 : 2 ≤ k - 1 := by omega
  have hkpred_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hRlt : erdosPosaR (k - 1) < erdosPosaR k :=
    erdosPosaR_pred_lt_of_four_le hk
  have hmul :
      ((k - 1 : ℕ) : ℝ) * erdosPosaR (k - 1) <
        ((k - 1 : ℕ) : ℝ) * erdosPosaR k :=
    mul_lt_mul_of_pos_left hRlt hkpred_pos
  have hlogS : logTwo (erdosPosaS k) ≤ erdosPosaR k :=
    logTwo_erdosPosaS_le_erdosPosaR_of_four_le hk
  have hcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    rw [show k = (k - 1) + 1 by omega]
    norm_num
  have hsum :
      ((k - 1 : ℕ) : ℝ) * erdosPosaR (k - 1) +
          logTwo (erdosPosaS k) <
        (k : ℝ) * erdosPosaR k := by
    rw [hcast]
    nlinarith
  simp [erdosPosaS, hk2, hkpred2] at hlogS ⊢
  simp [erdosPosaS, hk2] at hsum
  nlinarith

lemma erdosPosaS_pred_lt_sub_four_logTwo_two :
    erdosPosaS (2 - 1) <
      erdosPosaS 2 - 4 * logTwo (erdosPosaS 2) := by
  have hlog40 : logTwo (40 : ℝ) < (6 : ℝ) :=
    logTwo_lt_of_lt_two_pow_nat (x := (40 : ℝ)) (n := 6)
      (by norm_num) (by norm_num)
  norm_num [erdosPosaS, erdosPosaR]
  nlinarith

lemma logTwo_three_gt_three_halves :
    (3 / 2 : ℝ) < logTwo (3 : ℝ) := by
  have hlog3 : (13 / 12 : ℝ) ≤ Real.log 3 := by
    have h :=
      Real.sum_range_le_log_div (x := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) 2
    norm_num at h
    nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < (7 / 10 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  unfold logTwo
  rw [lt_div_iff₀ hlog2pos]
  nlinarith

lemma one_half_lt_logTwo_three_halves :
    (1 / 2 : ℝ) < logTwo (3 / 2 : ℝ) := by
  have hlog32 : (2 / 5 : ℝ) < Real.log (3 / 2 : ℝ) := by
    have h := Real.lt_log_one_add_of_pos (x := (1 / 2 : ℝ)) (by norm_num)
    norm_num at h
    nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < (7 / 10 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  unfold logTwo
  rw [lt_div_iff₀ hlog2pos]
  nlinarith

lemma six_lt_erdosPosaR_three : (6 : ℝ) < erdosPosaR 3 := by
  have hL : (3 / 2 : ℝ) < logTwo (3 : ℝ) :=
    logTwo_three_gt_three_halves
  have hlogL :
      (1 / 2 : ℝ) < logTwo (logTwo (3 : ℝ)) := by
    have hmono :
        logTwo (3 / 2 : ℝ) < logTwo (logTwo (3 : ℝ)) :=
      logTwo_strictMono (x := (3 / 2 : ℝ)) (y := logTwo (3 : ℝ))
        (by norm_num) hL
    exact one_half_lt_logTwo_three_halves.trans hmono
  change (6 : ℝ) <
    logTwo (3 : ℝ) + logTwo (logTwo (3 : ℝ)) + 4
  nlinarith

lemma erdosPosaR_three_lt_eight : erdosPosaR 3 < (8 : ℝ) := by
  have hLlt : logTwo (3 : ℝ) < (2 : ℝ) := by
    have h := logTwo_strictMono (x := (3 : ℝ)) (y := (4 : ℝ))
      (by norm_num) (by norm_num)
    simpa [logTwo_four] using h
  have hLgt : (1 : ℝ) ≤ logTwo (3 : ℝ) := by
    have h := logTwo_mono (x := (2 : ℝ)) (y := (3 : ℝ))
      (by norm_num) (by norm_num)
    simpa [logTwo_two] using h
  have hlogL : logTwo (logTwo (3 : ℝ)) ≤ logTwo (3 : ℝ) :=
    logTwo_le_self_of_one_le hLgt
  change
    logTwo (3 : ℝ) + logTwo (logTwo (3 : ℝ)) + 4 < (8 : ℝ)
  nlinarith

lemma erdosPosaS_pred_lt_sub_four_logTwo_three :
    erdosPosaS (3 - 1) <
      erdosPosaS 3 - 4 * logTwo (erdosPosaS 3) := by
  have hs3_gt : (72 : ℝ) < erdosPosaS 3 := by
    norm_num [erdosPosaS]
    nlinarith [six_lt_erdosPosaR_three]
  have hs3_lt : erdosPosaS 3 < (96 : ℝ) := by
    norm_num [erdosPosaS]
    nlinarith [erdosPosaR_three_lt_eight]
  have hs3_pos : 0 < erdosPosaS 3 := by nlinarith
  have hs3_lt_pow : erdosPosaS 3 < (2 : ℝ) ^ 7 := by
    norm_num
    nlinarith
  have hlogS : logTwo (erdosPosaS 3) < (7 : ℝ) :=
    logTwo_lt_of_lt_two_pow_nat (x := erdosPosaS 3) (n := 7)
      hs3_pos hs3_lt_pow
  have hs2 : erdosPosaS (3 - 1) = (40 : ℝ) := by
    norm_num [erdosPosaS, erdosPosaR]
  rw [hs2]
  nlinarith

lemma erdosPosaS_pred_lt_sub_four_logTwo {k : ℕ} (hk : 2 ≤ k) :
    erdosPosaS (k - 1) <
      erdosPosaS k - 4 * logTwo (erdosPosaS k) := by
  by_cases h2 : k = 2
  · subst k
    simpa using erdosPosaS_pred_lt_sub_four_logTwo_two
  by_cases h3 : k = 3
  · subst k
    simpa using erdosPosaS_pred_lt_sub_four_logTwo_three
  have hk4 : 4 ≤ k := by omega
  exact erdosPosaS_pred_lt_sub_four_logTwo_of_four_le hk4

/--
The remaining structural object in Diestel's proof: a cubic multigraph
obtained by suppressing the degree-two vertices of `G - U`, together with a
cycle-packing transfer back to `G - U`.
-/
def HasSuppressedCubicKernel (G : MultiGraph V E) [Finite V] [Finite E]
    (U : Set V) : Prop :=
  ∃ V' : Type u, ∃ E' : Type v,
    ∃ hfinV' : Finite V', ∃ hfinE' : Finite E',
    ∃ H : MultiGraph V' E',
      @IsCubic V' E' H hfinE' ∧
        (branchVertexSet G U).ncard ≤ H.vertexSet.ncard ∧
          CyclePackingTransfer H (G.deleteVerts U)

lemma deleteVerts_isCubic_of_all_outside_degree_three
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    {U : Set V}
    (hdeg3 : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      degree (G.deleteVerts U) v = 3) :
    IsCubic (G.deleteVerts U) := by
  refine ⟨deleteVerts_loopless (G := G) hCubic.1 U, ?_⟩
  intro v hv
  rw [Graph.vertexSet_deleteVerts] at hv
  exact hdeg3 v hv.1 hv.2

lemma branchVertexSet_subset_deleteVerts_vertexSet
    {G : MultiGraph V E} [Finite E] (U : Set V) :
    branchVertexSet G U ⊆ (G.deleteVerts U).vertexSet := by
  intro v hv
  rw [Graph.vertexSet_deleteVerts]
  exact ⟨hv.1, hv.2.1⟩

lemma hasSuppressedCubicKernel_of_all_outside_degree_three
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsCubic)
    {U : Set V}
    (hdeg3 : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      degree (G.deleteVerts U) v = 3) :
    HasSuppressedCubicKernel G U := by
  refine ⟨V, E, inferInstance, inferInstance, G.deleteVerts U, ?_, ?_, ?_⟩
  · exact deleteVerts_isCubic_of_all_outside_degree_three (G := G) hCubic hdeg3
  · exact Set.ncard_le_ncard (branchVertexSet_subset_deleteVerts_vertexSet (G := G) U)
  · intro k hpack
    exact hpack

lemma all_outside_degree_three_of_terminal_degreeTwoOutside_eq_empty
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ degree (G.deleteVerts U) v)
    (hD₂ : degreeTwoOutsideSet G U = ∅) :
    ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      degree (G.deleteVerts U) v = 3 := by
  intro v hvG hvU
  have hge : 2 ≤ degree (G.deleteVerts U) v := hterminal v hvG hvU
  have hle : degree (G.deleteVerts U) v ≤ 3 :=
    deleteVerts_degree_le_three_of_cubic (G := G) hCubic hvG
  have hdeg : degree (G.deleteVerts U) v = 2 ∨
      degree (G.deleteVerts U) v = 3 := by omega
  rcases hdeg with hdeg | hdeg
  · have hvD : v ∈ degreeTwoOutsideSet G U := ⟨hvG, hvU, hdeg⟩
    rw [hD₂] at hvD
    simp at hvD
  · exact hdeg

lemma hasSuppressedCubicKernel_of_terminal_degreeTwoOutside_eq_empty
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsCubic)
    {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ degree (G.deleteVerts U) v)
    (hD₂ : degreeTwoOutsideSet G U = ∅) :
    HasSuppressedCubicKernel G U :=
  hasSuppressedCubicKernel_of_all_outside_degree_three (G := G) hCubic
    (all_outside_degree_three_of_terminal_degreeTwoOutside_eq_empty
      (G := G) hCubic hterminal hD₂)

theorem hasCyclePackingReduction_of_suppressed_kernel
    {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (hk : 2 ≤ k)
    (hAnalytic :
      erdosPosaS (k - 1) < erdosPosaS k - 4 * logTwo (erdosPosaS k))
    (hKernel : ∀ C : G.CycleIn, ∀ U : Set V,
      C.support ⊆ U →
        U ⊆ G.vertexSet →
          U.ncard + (G.edgeBoundary U).ncard ≤
            C.support.ncard + (G.edgeBoundary C.support).ncard →
            (∀ v : V, v ∈ G.vertexSet → v ∉ U →
              2 ≤ degree (G.deleteVerts U) v) →
              HasSuppressedCubicKernel G U) :
    G.IsCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        HasCyclePackingReduction G k := by
  classical
  intro hCubic hLarge
  obtain ⟨C, hCshort⟩ :=
    exists_cycle_support_ncard_lt_log_bound_of_erdosPosaS_lt
      (G := G) hk hCubic hLarge
  obtain ⟨U, hCU, hUV, hscore, hterminal⟩ :=
    exists_pruned_superset_of_cycle_support_with_score
      (G := G) hCubic C
  obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranchH, htransferU⟩ :=
    hKernel C U hCU hUV hscore hterminal
  haveI : Finite V' := hfinV'
  haveI : Finite E' := hfinE'
  have hsix : (6 : ℝ) ≤ erdosPosaS k :=
    (six_lt_erdosPosaS hk).le
  have hmono :
      erdosPosaS k - 4 * logTwo (erdosPosaS k) ≤
        (G.vertexSet.ncard : ℝ) - 4 * logTwo (G.vertexSet.ncard : ℝ) :=
    sub_four_logTwo_mono_on_six hsix hLarge.le
  have hbefore_log :
      erdosPosaS (k - 1) <
        (G.vertexSet.ncard : ℝ) - 4 * logTwo (G.vertexSet.ncard : ℝ) :=
    hAnalytic.trans_le hmono
  have hCshort' :
      (C.support.ncard : ℝ) <
        2 * logTwo (G.vertexSet.ncard : ℝ) := by
    simpa [logTwo] using hCshort
  have hbefore_cycle :
      erdosPosaS (k - 1) <
        (G.vertexSet.ncard : ℝ) - 2 * (C.support.ncard : ℝ) := by
    nlinarith
  have htwoc_lt_n :
      2 * C.support.ncard < G.vertexSet.ncard := by
    have hs_nonneg : 0 ≤ erdosPosaS (k - 1) := erdosPosaS_nonneg (k - 1)
    by_contra hnot
    have hnle : G.vertexSet.ncard ≤ 2 * C.support.ncard := Nat.le_of_not_gt hnot
    have hnle_real :
        (G.vertexSet.ncard : ℝ) ≤ 2 * (C.support.ncard : ℝ) := by
      exact_mod_cast hnle
    nlinarith
  have htwoc_le_n : 2 * C.support.ncard ≤ G.vertexSet.ncard :=
    htwoc_lt_n.le
  have hbranchLowerNat :
      G.vertexSet.ncard - 2 * C.support.ncard ≤
        (branchVertexSet G U).ncard :=
    branchVertexSet_ncard_ge_sub_two_cycle
      (G := G) hCubic C hUV hscore hterminal
  have hbranchLowerReal :
      ((G.vertexSet.ncard - 2 * C.support.ncard : ℕ) : ℝ) ≤
        ((branchVertexSet G U).ncard : ℝ) := by
    exact_mod_cast hbranchLowerNat
  have hsub_cast :
      ((G.vertexSet.ncard - 2 * C.support.ncard : ℕ) : ℝ) =
        (G.vertexSet.ncard : ℝ) - 2 * (C.support.ncard : ℝ) := by
    rw [Nat.cast_sub htwoc_le_n]
    norm_num
  have hbranchLarge :
      erdosPosaS (k - 1) < ((branchVertexSet G U).ncard : ℝ) := by
    rw [hsub_cast] at hbranchLowerReal
    exact hbefore_cycle.trans_le hbranchLowerReal
  have hHLarge : erdosPosaS (k - 1) < (H.vertexSet.ncard : ℝ) := by
    have hbranchHReal :
        ((branchVertexSet G U).ncard : ℝ) ≤ (H.vertexSet.ncard : ℝ) := by
      exact_mod_cast hbranchH
    exact hbranchLarge.trans_le hbranchHReal
  let htransferDelete :
      CyclePackingTransfer (G.deleteVerts U) (G.deleteVerts C.support) :=
    cyclePackingTransfer_deleteVerts_of_subset (G := G) hCU
  refine ⟨C, V', E', hfinV', hfinE', H, hHCubic, hHLarge, ?_⟩
  intro l hpack
  exact htransferDelete l (htransferU l hpack)

theorem hasCyclePackingReduction_of_suppressed_kernel'
    {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (hk : 2 ≤ k)
    (hKernel : ∀ C : G.CycleIn, ∀ U : Set V,
      C.support ⊆ U →
        U ⊆ G.vertexSet →
          U.ncard + (G.edgeBoundary U).ncard ≤
            C.support.ncard + (G.edgeBoundary C.support).ncard →
            (∀ v : V, v ∈ G.vertexSet → v ∉ U →
              2 ≤ degree (G.deleteVerts U) v) →
              HasSuppressedCubicKernel G U) :
    G.IsCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        HasCyclePackingReduction G k :=
  hasCyclePackingReduction_of_suppressed_kernel (G := G) hk
    (erdosPosaS_pred_lt_sub_four_logTwo hk) hKernel

end MultiGraph

end Chapter02
end Diestel
