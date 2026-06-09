import Chapter01.definitions_ch1
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.all false

namespace Diestel
namespace Chapter01

/--
The logarithm of the AHL factor `(x - 1)^x`.

The Alon-Hoory-Linial proof uses that `x ↦ (x - 1)^x` is log-convex
on `[2,∞)`, equivalently that this function is convex.
-/
noncomputable def ahlPhi (x : ℝ) : ℝ :=
  x * Real.log (x - 1)

noncomputable def ahlPhiDeriv (x : ℝ) : ℝ :=
  Real.log (x - 1) + x / (x - 1)

theorem ahlPhi_hasDerivAt {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt ahlPhi (ahlPhiDeriv x) x := by
  unfold ahlPhi ahlPhiDeriv
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (x - 1)) x := by
    simpa using ((hasDerivAt_id x).sub_const 1).log (by simpa using sub_ne_zero.mpr hx)
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  convert hid.mul hlog using 1
  ring

theorem deriv_ahlPhi_eq {x : ℝ} (hx : x ≠ 1) :
    deriv ahlPhi x = ahlPhiDeriv x :=
  (ahlPhi_hasDerivAt hx).deriv

theorem ahlPhiDeriv_hasDerivAt {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt ahlPhiDeriv ((x - 2) / (x - 1)^2) x := by
  unfold ahlPhiDeriv
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x - 1)) (1 / (x - 1)) x := by
    simpa using ((hasDerivAt_id x).sub_const 1).log (by simpa using sub_ne_zero.mpr hx)
  have hquot : HasDerivAt (fun x : ℝ => x / (x - 1)) (-1 / (x - 1)^2) x := by
    have hnum : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
    have hden : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
    convert hnum.div hden (by simpa using sub_ne_zero.mpr hx) using 1
    ring
  convert hlog.add hquot using 1
  field_simp [sub_ne_zero.mpr hx]
  ring

theorem ahlPhi_continuousOn_Ici_two :
    ContinuousOn ahlPhi (Set.Ici (2 : ℝ)) := by
  unfold ahlPhi
  have hsub : ContinuousOn (fun x : ℝ => x - 1) (Set.Ici (2 : ℝ)) :=
    continuousOn_id.sub continuousOn_const
  have hlog : ContinuousOn (fun x : ℝ => Real.log (x - 1)) (Set.Ici (2 : ℝ)) :=
    hsub.log (by
      intro x hx
      have hx2 : 2 ≤ x := hx
      nlinarith)
  exact continuousOn_id.mul hlog

theorem ahlPhi_differentiableOn_Ioi_two :
    DifferentiableOn ℝ ahlPhi (Set.Ioi (2 : ℝ)) := by
  unfold ahlPhi
  have hsub : DifferentiableOn ℝ (fun x : ℝ => x - 1) (Set.Ioi (2 : ℝ)) :=
    differentiableOn_id.sub (differentiableOn_const 1)
  have hlog : DifferentiableOn ℝ (fun x : ℝ => Real.log (x - 1)) (Set.Ioi (2 : ℝ)) :=
    hsub.log (by
      intro x hx
      have hx2 : 2 < x := hx
      nlinarith)
  exact differentiableOn_id.mul hlog

theorem ahlPhiDeriv_differentiableOn_Ioi_two :
    DifferentiableOn ℝ ahlPhiDeriv (Set.Ioi (2 : ℝ)) := by
  unfold ahlPhiDeriv
  have hsub : DifferentiableOn ℝ (fun x : ℝ => x - 1) (Set.Ioi (2 : ℝ)) :=
    differentiableOn_id.sub (differentiableOn_const 1)
  have hlog : DifferentiableOn ℝ (fun x : ℝ => Real.log (x - 1)) (Set.Ioi (2 : ℝ)) :=
    hsub.log (by
      intro x hx
      have hx2 : 2 < x := hx
      nlinarith)
  have hquot : DifferentiableOn ℝ (fun x : ℝ => x / (x - 1)) (Set.Ioi (2 : ℝ)) :=
    differentiableOn_id.div hsub (by
      intro x hx
      have hx2 : 2 < x := hx
      nlinarith)
  exact hlog.add hquot

theorem deriv_ahlPhi_differentiableOn_Ioi_two :
    DifferentiableOn ℝ (deriv ahlPhi) (Set.Ioi (2 : ℝ)) := by
  apply ahlPhiDeriv_differentiableOn_Ioi_two.congr
  intro x hx
  have hx2 : 2 < x := hx
  exact deriv_ahlPhi_eq (by nlinarith)

theorem deriv2_ahlPhi_eq {x : ℝ} (hx : 2 < x) :
    deriv^[2] ahlPhi x = (x - 2) / (x - 1)^2 := by
  have hxne : x ≠ 1 := by nlinarith
  have hev : (fun y => deriv ahlPhi y) =ᶠ[nhds x] ahlPhiDeriv := by
    exact (eventually_ne_nhds hxne).mono (by
      intro y hy
      exact deriv_ahlPhi_eq hy)
  have hderiv : HasDerivAt (fun y => deriv ahlPhi y) ((x - 2) / (x - 1)^2) x :=
    (ahlPhiDeriv_hasDerivAt hxne).congr_of_eventuallyEq hev
  simpa [Function.iterate_succ] using hderiv.deriv

theorem ahlPhi_deriv2_nonneg {x : ℝ} (hx : x ∈ interior (Set.Ici (2 : ℝ))) :
    0 ≤ deriv^[2] ahlPhi x := by
  rw [interior_Ici] at hx
  have hx2 : 2 < x := hx
  rw [deriv2_ahlPhi_eq hx2]
  apply div_nonneg
  · nlinarith
  · exact sq_nonneg (x - 1)

theorem ahlPhi_convexOn_Ici_two :
    ConvexOn ℝ (Set.Ici (2 : ℝ)) ahlPhi := by
  apply convexOn_of_deriv2_nonneg
  · exact convex_Ici 2
  · exact ahlPhi_continuousOn_Ici_two
  · simpa [interior_Ici] using ahlPhi_differentiableOn_Ioi_two
  · simpa [interior_Ici] using deriv_ahlPhi_differentiableOn_Ioi_two
  · intro x hx
    exact ahlPhi_deriv2_nonneg hx

theorem ahlPhi_weighted_average_le_sum {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 2 ≤ x i) :
    ahlPhi (∑ i ∈ s, w i * x i) ≤ ∑ i ∈ s, w i * ahlPhi (x i) := by
  simpa [smul_eq_mul] using
    (ahlPhi_convexOn_Ici_two.map_sum_le (t := s) (w := w) (p := x)
      hw hw_sum (by
        intro i hi
        exact hx i hi))

theorem ahlPhi_average_le_average {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hs : s.Nonempty) (hx : ∀ i ∈ s, 2 ≤ x i) :
    ahlPhi ((s.card : ℝ)⁻¹ * ∑ i ∈ s, x i) ≤
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, ahlPhi (x i) := by
  have hcard_pos_nat : 0 < s.card := Finset.card_pos.mpr hs
  have hcard_ne : (s.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcard_pos_nat)
  have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hweights : ∀ i ∈ s, 0 ≤ ((s.card : ℝ)⁻¹) := by
    intro i hi
    exact inv_nonneg.mpr (le_of_lt hcard_pos)
  have hweights_sum : ∑ i ∈ s, ((s.card : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const]
    simp [hcard_ne]
  have h := ahlPhi_weighted_average_le_sum s (fun _ => (s.card : ℝ)⁻¹) x
    hweights hweights_sum hx
  rw [Finset.mul_sum, Finset.mul_sum]
  exact h

theorem average_degree_real_eq_inv_card_mul_sum_degrees {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    ((average_degree G : ℚ) : ℝ) =
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V, (G.degree v : ℝ) := by
  rw [average_degree]
  rw [Rat.cast_div]
  rw [Rat.cast_natCast]
  rw [Rat.cast_sum]
  simp [div_eq_inv_mul]

theorem ahlPhi_average_degree_le_average_phi_degrees {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ahlPhi ((average_degree G : ℚ) : ℝ) ≤
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V, ahlPhi (G.degree v : ℝ) := by
  rw [average_degree_real_eq_inv_card_mul_sum_degrees G]
  apply ahlPhi_average_le_average Finset.univ
  · exact Finset.univ_nonempty
  · intro v hv
    exact_mod_cast hdeg v

/--
The logarithm of the AHL branching factor
`Λ = ∏ v, (degree v - 1) ^ (degree v / (|V| * average_degree G))`.

Writing it additively avoids committing to a particular real-power product API
while proving the convexity/Jensen part of the AHL argument.
-/
noncomputable def ahlLogLambda {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : ℝ :=
  (((average_degree G : ℚ) : ℝ))⁻¹ *
    ((Fintype.card V : ℝ)⁻¹ * ∑ v : V, ahlPhi (G.degree v : ℝ))

theorem log_average_degree_sub_one_le_ahlLogLambda {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (havg : 2 ≤ ((average_degree G : ℚ) : ℝ))
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    Real.log (((average_degree G : ℚ) : ℝ) - 1) ≤ ahlLogLambda G := by
  let a : ℝ := ((average_degree G : ℚ) : ℝ)
  have ha_pos : 0 < a := by linarith
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hJ := ahlPhi_average_degree_le_average_phi_degrees G hdeg
  dsimp [ahlPhi] at hJ
  dsimp [ahlLogLambda]
  change Real.log (a - 1) ≤ a⁻¹ * ((Fintype.card V : ℝ)⁻¹ *
      ∑ v : V, ahlPhi (G.degree v : ℝ))
  have hmul := mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr (le_of_lt ha_pos))
  change a⁻¹ * (a * Real.log (a - 1)) ≤
      a⁻¹ * ((Fintype.card V : ℝ)⁻¹ * ∑ v : V, ahlPhi (G.degree v : ℝ)) at hmul
  have hleft : a⁻¹ * (a * Real.log (a - 1)) = Real.log (a - 1) := by
    field_simp [ha_ne]
  rwa [hleft] at hmul

/-- The AHL branching factor `Λ`, written as the exponential of `ahlLogLambda`. -/
noncomputable def ahlLambda {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : ℝ :=
  Real.exp (ahlLogLambda G)

theorem average_degree_sub_one_le_ahlLambda {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (havg : 2 ≤ ((average_degree G : ℚ) : ℝ))
    (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ((average_degree G : ℚ) : ℝ) - 1 ≤ ahlLambda G := by
  have hlog := log_average_degree_sub_one_le_ahlLogLambda G havg hdeg
  have hpos : 0 < ((average_degree G : ℚ) : ℝ) - 1 := by linarith
  calc
    ((average_degree G : ℚ) : ℝ) - 1 = Real.exp (Real.log (((average_degree G : ℚ) : ℝ) - 1)) := by
      rw [Real.exp_log hpos]
    _ ≤ Real.exp (ahlLogLambda G) := Real.exp_monotone hlog
    _ = ahlLambda G := rfl

theorem n0_mono_degree {d e : ℝ} {g : ℕ} (hd : 2 ≤ d) (hde : d ≤ e) :
    n0 d g ≤ n0 e g := by
  let r := g / 2
  have he : 2 ≤ e := hd.trans hde
  have hd_nonneg : 0 ≤ d := by linarith
  have he_nonneg : 0 ≤ e := by linarith
  have hd_sub_nonneg : 0 ≤ d - 1 := by linarith
  have he_sub_nonneg : 0 ≤ e - 1 := by linarith
  have hsub_le : d - 1 ≤ e - 1 := by linarith
  have hpow_le : ∀ i : ℕ, (d - 1) ^ i ≤ (e - 1) ^ i := fun i =>
    pow_le_pow_left₀ hd_sub_nonneg hsub_le i
  have hsum_le :
      (∑ i ∈ Finset.range r, (d - 1) ^ i) ≤
        ∑ i ∈ Finset.range r, (e - 1) ^ i := by
    exact Finset.sum_le_sum (fun i hi => hpow_le i)
  have hsum_d_nonneg : 0 ≤ ∑ i ∈ Finset.range r, (d - 1) ^ i := by
    exact Finset.sum_nonneg (fun i hi => pow_nonneg hd_sub_nonneg i)
  have hsum_e_nonneg : 0 ≤ ∑ i ∈ Finset.range r, (e - 1) ^ i := by
    exact Finset.sum_nonneg (fun i hi => pow_nonneg he_sub_nonneg i)
  unfold n0
  dsimp only
  split
  · gcongr
  · gcongr

end Chapter01
end Diestel
