import «statements-and-proofs».ChekuriChuzhoyCorollary32Contract
import «statements-and-proofs».ChekuriChuzhoyStitchedRows

/-!
# Downstream Chekuri--Chuzhoy contract adapter

The named paper contracts are split across:

* `ChekuriChuzhoyTheorem215Contract`
* `ChekuriChuzhoyTheoremB1Contract`
* `ChekuriChuzhoyTheorem31Contract`
* `ChekuriChuzhoyCorollary32Contract`

This file keeps the narrow specialized interface consumed by the existing
Appendix C.1 formalization in `ChekuriChuzhoy.lean`: Corollary 3.2 at the exact
parameters used in Corollary 3.3, returning either a direct grid minor or the
stitched-row object already handled by the full proof file.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyContract

universe u

/-- Chekuri--Chuzhoy Corollary 3.2, specialized to the parameters used in
Corollary 3.3 and to the stitched-row data consumed by the Appendix C.1
assembly proof.

This is an adapter from the broader Corollary 3.2 contract, not a separate
paper axiom. -/
theorem gridMinor_or_stitchedRows_of_pathOfSets :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {g : ℕ},
        2 ≤ g →
          (P : StrongPathOfSetsSystem G (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g)) →
            ContainsGridMinor G g ∨
              Nonempty
                (ChekuriChuzhoy.StitchedRows G g (16 * g ^ 2 + 10 * g)
                  P.toPathOfSetsSystem) := by
  intro V hVfin hVdec G g hg P
  letI : Fintype V := hVfin
  letI : DecidableEq V := hVdec
  have hell : 2 ≤ 2 * g * (g - 1) := by
    have hNpos : 0 < g * (g - 1) :=
      ChekuriChuzhoy.evenClusterOrdinal_count_pos_of_two_le hg
    have hN : 1 ≤ g * (g - 1) := Nat.succ_le_of_lt hNpos
    calc
      2 = 2 * 1 := by omega
      _ ≤ 2 * (g * (g - 1)) := Nat.mul_le_mul_left 2 hN
      _ = 2 * g * (g - 1) := by rw [Nat.mul_assoc]
  have hg_gt : 1 < g := lt_of_lt_of_le (by decide : 1 < 2) hg
  have hw : (16 * g + 10) * g ≤ 16 * g ^ 2 + 10 * g := by
    have hwidth : (16 * g + 10) * g = 16 * g ^ 2 + 10 * g := by
      ring
    exact le_of_eq hwidth
  rcases corollary32_gridMinor_or_routedRows G hell hg_gt hg_gt hw
      P.toPathOfSetsSystem with hgrid | hrows
  · exact Or.inl hgrid
  · rcases hrows with ⟨R⟩
    refine Or.inr ⟨{
      rows := R.rows
      rows_card := R.rows_card
      row_trace_cluster := R.row_trace_cluster
      row_clusters_ordered := R.row_clusters_ordered
      bridge_in_even_cluster := ?_
    }⟩
    intro i
    refine R.bridge_in_even_cluster (ChekuriChuzhoy.evenClusterIndex g i) ?_
    have hval :
        (ChekuriChuzhoy.evenClusterIndex g i).1 + 1 =
          2 * (i.1 + 1) := by
      simp [ChekuriChuzhoy.evenClusterIndex]
      omega
    rw [hval]
    exact Nat.mul_mod_right 2 (i.1 + 1)

end ChekuriChuzhoyContract
end SimpleGraph
