import Chapter01.definitions_ch1
import Chapter01.proposition_1_9_2
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

private lemma atomic_cut_eq_incidence {V : Type u} (G : SimpleGraph V) (v : V) :
    atomic_cut G v = {e : G.edgeSet | v ∈ (e : Sym2 V)} := by
  ext e
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    change v ∈ (e : Sym2 V)
    rw [hxy]
    simp at hx
    subst x
    simp [Sym2.mem_iff]
  · intro hv
    refine ⟨v, by simp, Sym2.Mem.other hv, ?_, ?_⟩
    · intro hother
      have hdiag : (e : Sym2 V) = s(v, v) := by
        rw [← Sym2.other_spec hv, hother]
      have hloop : G.Adj v v := by
        simpa [SimpleGraph.mem_edgeSet, hdiag] using e.2
      exact hloop.ne rfl
    · exact (Sym2.other_spec hv).symm

private lemma edge_indicator_atomic_cut_apply {V : Type u} (G : SimpleGraph V)
    [DecidableEq V] (v : V) (e : G.edgeSet) :
    edge_indicator G (atomic_cut G v) e = if v ∈ (e : Sym2 V) then 1 else 0 := by
  classical
  rw [atomic_cut_eq_incidence]
  by_cases hv : v ∈ (e : Sym2 V) <;> simp [edge_indicator, hv]

theorem cut_space_incidence_image {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] :
    ∀ D : EdgeSpace G,
      D ∈ cut_space G ↔
        ∃ U : VertexSpace V,
          ∀ e : G.edgeSet,
            D e = ∑ v : V, (if v ∈ (e : Sym2 V) then U v else 0) := by
  classical
  intro D
  have hspan := (proposition_1_9_2 G).2
  rw [hspan]
  constructor
  · intro hD
    change D ∈ Submodule.span (ZMod 2)
      {D : EdgeSpace G | ∃ v : V, D = edge_indicator G (atomic_cut G v)} at hD
    induction hD using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨v, rfl⟩
        refine ⟨Pi.single v 1, ?_⟩
        intro e
        rw [edge_indicator_atomic_cut_apply]
        by_cases hv : v ∈ (e : Sym2 V)
        · rw [if_pos hv]
          rw [Finset.sum_eq_single v]
          · simp [hv, Pi.single]
          · intro w _ hwv
            by_cases hw : w ∈ (e : Sym2 V) <;> simp [hw, Pi.single, hwv]
          · intro hvnot
            exact (hvnot (Finset.mem_univ v)).elim
        · rw [if_neg hv]
          rw [Finset.sum_eq_zero]
          intro w _
          by_cases hw : w ∈ (e : Sym2 V)
          · have hwv : w ≠ v := fun h => hv (h ▸ hw)
            simp [hw, Pi.single, hwv]
          · simp [hw]
    | zero =>
        refine ⟨0, ?_⟩
        intro e
        simp
    | add x y _ _ hx hy =>
        rcases hx with ⟨Ux, hUx⟩
        rcases hy with ⟨Uy, hUy⟩
        refine ⟨Ux + Uy, ?_⟩
        intro e
        rw [Pi.add_apply, hUx e, hUy e]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
    | smul a x _ hx =>
        fin_cases a
        · refine ⟨0, ?_⟩
          intro e
          change (0 : ZMod 2) • x e =
            ∑ v : V, (if v ∈ (e : Sym2 V) then (0 : VertexSpace V) v else 0)
          simp
        · rcases hx with ⟨Ux, hUx⟩
          refine ⟨Ux, ?_⟩
          intro e
          change (1 : ZMod 2) • x e =
            ∑ v : V, (if v ∈ (e : Sym2 V) then Ux v else 0)
          simpa using hUx e
  · rintro ⟨U, hU⟩
    have hDsum : D = ∑ v : V, U v • edge_indicator G (atomic_cut G v) := by
      ext e
      rw [hU e]
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro v _
      rw [Pi.smul_apply, edge_indicator_atomic_cut_apply]
      by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
    rw [hDsum]
    exact Submodule.sum_mem _ fun v _ =>
      Submodule.smul_mem _ (U v) <|
        Submodule.subset_span
          (show edge_indicator G (atomic_cut G v) ∈
            {D : EdgeSpace G | ∃ v : V, D = edge_indicator G (atomic_cut G v)} from
            ⟨v, rfl⟩)

end Chapter01
end Diestel
