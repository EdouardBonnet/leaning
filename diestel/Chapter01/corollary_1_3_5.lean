import Chapter01.proposition_1_3_1
import Chapter01.moore_bound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private theorem odd_log_bound_of_count {N r : ℕ} (hr : 0 < r)
    (hN : 3 * 2 ^ (r - 1) ≤ N) :
    ((2 * r + 1 : ℕ) : ℝ) < 2 * (Real.log (N : ℝ) / Real.log 2) := by
  have hbase_le_real : ((3 * 2 ^ (r - 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hlog_le :
      Real.log ((3 * 2 ^ (r - 1) : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) hbase_le_real
  have hlog_base :
      Real.log ((3 * 2 ^ (r - 1) : ℕ) : ℝ) =
        Real.log 3 + ((r - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_mul, Real.log_pow]
    · norm_num
    · positivity
    · positivity
  have hfixed : 3 * Real.log 2 < 2 * Real.log 3 := by
    have hlog : Real.log ((2 : ℝ) ^ 3) < Real.log ((3 : ℝ) ^ 2) := by
      apply Real.log_lt_log
      · positivity
      · norm_num
    rw [Real.log_pow, Real.log_pow] at hlog
    norm_num at hlog
    exact hlog
  have htwice_lower :
      2 * (Real.log 3 + ((r - 1 : ℕ) : ℝ) * Real.log 2) ≤
        2 * Real.log (N : ℝ) := by
    nlinarith
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hmain : ((2 * r + 1 : ℕ) : ℝ) * Real.log 2 <
      2 * Real.log (N : ℝ) := by
    have hr_real : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      have hr_eq : r = (r - 1) + 1 := by omega
      rw [hr_eq]
      norm_num
    have hgcast : ((2 * r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + 1 := by
      norm_num
    rw [hr_real] at htwice_lower
    rw [hgcast]
    nlinarith
  have hdiv : ((2 * r + 1 : ℕ) : ℝ) <
      (2 * Real.log (N : ℝ)) / Real.log 2 := by
    rw [lt_div_iff₀ hlog2pos]
    exact hmain
  simpa [mul_div_assoc] using hdiv

private theorem even_log_bound_of_two_pow_lt {N r : ℕ} (hN : 2 ^ r < N) :
    ((2 * r : ℕ) : ℝ) < 2 * (Real.log (N : ℝ) / Real.log 2) := by
  have hpow_real : ((2 : ℝ) ^ r) < (N : ℝ) := by
    exact_mod_cast hN
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ r) hpow_real
  rw [Real.log_pow] at hlog
  have hlog2pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hmain : ((2 * r : ℕ) : ℝ) * Real.log 2 < 2 * Real.log (N : ℝ) := by
    have hcast : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by
      norm_num
    rw [hcast]
    nlinarith
  have hdiv : ((2 * r : ℕ) : ℝ) <
      (2 * Real.log (N : ℝ)) / Real.log 2 := by
    rw [lt_div_iff₀ hlog2pos]
    exact hmain
  simpa [mul_div_assoc] using hdiv

/--
Diestel, Corollary 1.3.5.
If `δ(G) ≥ 3`, then `g(G) < 2 log |G|`, where Diestel's `log` has base 2.
-/
theorem corollary_1_3_5 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  3 ≤ G.minDegree →
    (G.girth : ℝ) < 2 * (Real.log (Fintype.card V) / Real.log 2) := by
  classical
  intro hmin
  letI : DecidableEq V := Classical.decEq V
  have hnonempty : Nonempty V := by
    by_contra hnone
    haveI : IsEmpty V := not_nonempty_iff.mp hnone
    simp at hmin
  letI : Nonempty V := hnonempty
  have hnot_acyclic : ¬ G.IsAcyclic := by
    intro hacy
    obtain ⟨a, c, hc, _hlen⟩ :=
      (proposition_1_3_1 G).2 (by omega : 2 ≤ G.minDegree)
    exact hacy c hc
  have hgirth_egirth : (G.girth : ℕ∞) ≤ G.egirth := by
    exact G.egirth.coe_toNat_le_self
  have hg3 : 3 ≤ G.girth := SimpleGraph.three_le_girth hnot_acyclic
  by_cases hodd : Odd G.girth
  · let r := G.girth / 2
    have hrpos : 0 < r := by
      rcases hodd with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    have hsmall : r + r < G.girth := by
      rcases hodd with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    let z : V := Classical.choice hnonempty
    have hcount :
        3 * 2 ^ (r - 1) ≤ Fintype.card V :=
      three_mul_two_pow_pred_le_card_of_minDegree_girth G hgirth_egirth hmin
        (z := z) hrpos hsmall
    have hlog :=
      odd_log_bound_of_count (N := Fintype.card V) (r := r) hrpos hcount
    have hg_eq : G.girth = 2 * r + 1 := by
      rcases hodd with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    simpa [hg_eq] using hlog
  · have heven : Even G.girth := Nat.not_odd_iff_even.mp hodd
    let r := G.girth / 2
    have hrpos : 0 < r - 1 := by
      rcases heven with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    have hsmall : (r - 1) + (r - 1) < G.girth := by
      rcases heven with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    have hcross : (r - 1) + ((r - 1) + 1) < G.girth := by
      rcases heven with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    let x : V := Classical.choice hnonempty
    have hdegx : 3 ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
    have hneigh_nonempty : (G.neighborFinset x).Nonempty := by
      rw [← Finset.card_pos, SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨y, hy⟩ := hneigh_nonempty
    have hxy : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
    have hcount :
        2 * 2 ^ (r - 1) < Fintype.card V :=
      two_mul_two_pow_lt_card_of_edgeRoot G hgirth_egirth hmin hxy hrpos hsmall hcross
    have hpow : 2 ^ r < Fintype.card V := by
      have hr_eq : r = (r - 1) + 1 := by omega
      rw [hr_eq, pow_succ]
      simpa [Nat.mul_comm] using hcount
    have hlog :=
      even_log_bound_of_two_pow_lt (N := Fintype.card V) (r := r) hpow
    have hg_eq : G.girth = 2 * r := by
      rcases heven with ⟨k, hk⟩
      dsimp [r]
      rw [hk]
      omega
    simpa [hg_eq] using hlog

end Chapter01
end Diestel

