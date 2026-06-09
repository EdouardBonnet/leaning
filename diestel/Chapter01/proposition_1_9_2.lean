import Chapter01.definitions_ch1
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

private noncomputable def vertsIn {V : Type u} [Fintype V] (A : Set V) : Finset V :=
  letI := Classical.decPred (fun v : V => v ∈ A)
  Finset.univ.filter fun v => v ∈ A

private lemma mem_vertsIn {V : Type u} [Fintype V] {A : Set V} {v : V} :
    v ∈ vertsIn A ↔ v ∈ A := by
  classical
  simp [vertsIn]

private lemma edge_indicator_empty {V : Type u} (G : SimpleGraph V) :
    edge_indicator G (∅ : Set G.edgeSet) = 0 := by
  classical
  ext e
  simp [edge_indicator]

private lemma cut_edges_empty {V : Type u} (G : SimpleGraph V) :
    cut_edges G (∅ : Set V) = ∅ := by
  ext e
  simp [cut_edges]

private lemma cut_edges_univ {V : Type u} (G : SimpleGraph V) :
    cut_edges G (Set.univ : Set V) = ∅ := by
  ext e
  simp [cut_edges]

private lemma cut_vector_empty {V : Type u} (G : SimpleGraph V) :
    cut_vector G (∅ : Set V) = 0 := by
  rw [cut_vector, cut_edges_empty, edge_indicator_empty]

private lemma cut_vector_univ {V : Type u} (G : SimpleGraph V) :
    cut_vector G (Set.univ : Set V) = 0 := by
  rw [cut_vector, cut_edges_univ, edge_indicator_empty]

private lemma cut_vector_mem_cut_space {V : Type u} (G : SimpleGraph V) (A : Set V) :
    cut_vector G A ∈ cut_space G := by
  exact Submodule.subset_span ⟨A, rfl⟩

private lemma edge_indicator_mem_cut_space_of_isCut {V : Type u} (G : SimpleGraph V)
    {F : Set G.edgeSet} (hF : IsCut G F) :
    edge_indicator G F ∈ cut_space G := by
  rcases hF with ⟨A, _hA, _hAc, rfl⟩
  exact cut_vector_mem_cut_space G A

private lemma cut_vector_list_repr {V : Type u} (G : SimpleGraph V) (A : Set V) :
    ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        cut_vector G A = cuts.foldr (fun F acc => edge_indicator G F + acc) 0 := by
  classical
  by_cases hA : A.Nonempty
  · by_cases hAc : Aᶜ.Nonempty
    · refine ⟨[cut_edges G A], ?_, ?_⟩
      · intro F hF
        simp only [List.mem_singleton] at hF
        subst F
        exact Or.inl ⟨A, hA, hAc, rfl⟩
      · simp [cut_vector]
    · have hAuniv : A = Set.univ := by
        rw [← Set.compl_empty_iff]
        exact Set.not_nonempty_iff_eq_empty.mp hAc
      refine ⟨[], ?_, ?_⟩
      · simp
      · subst A
        simp [cut_vector_univ]
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    refine ⟨[], ?_, ?_⟩
    · simp
    · subst A
      simp [cut_vector_empty]

private lemma list_repr_zero {V : Type u} (G : SimpleGraph V) :
    ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        (0 : EdgeSpace G) = cuts.foldr (fun F acc => edge_indicator G F + acc) 0 := by
  exact ⟨[], by simp, by simp⟩

private lemma list_repr_add {V : Type u} (G : SimpleGraph V)
    {D E : EdgeSpace G}
    (hD : ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0)
    (hE : ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        E = cuts.foldr (fun F acc => edge_indicator G F + acc) 0) :
    ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        D + E = cuts.foldr (fun F acc => edge_indicator G F + acc) 0 := by
  rcases hD with ⟨cutsD, hcutsD, rfl⟩
  rcases hE with ⟨cutsE, hcutsE, rfl⟩
  refine ⟨cutsD ++ cutsE, ?_, ?_⟩
  · intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact hcutsD F hF
    · exact hcutsE F hF
  · induction cutsD with
    | nil =>
        simp
    | cons F Fs ih =>
        have htail : ∀ E ∈ Fs, IsCut G E ∨ E = ∅ := by
          intro E hE
          exact hcutsD E (by simp [hE])
        have ih' := ih htail
        simp only [List.foldr_cons]
        rw [add_assoc]
        rw [ih']
        rfl

private lemma list_repr_smul {V : Type u} (G : SimpleGraph V) (a : ZMod 2)
    {D : EdgeSpace G}
    (hD : ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0) :
    ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        a • D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0 := by
  fin_cases a
  · rcases list_repr_zero G with ⟨cuts, hcuts, hzero⟩
    refine ⟨cuts, hcuts, ?_⟩
    change (0 : ZMod 2) • D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0
    rw [zero_smul]
    exact hzero
  · rcases hD with ⟨cuts, hcuts, hD⟩
    refine ⟨cuts, hcuts, ?_⟩
    change (1 : ZMod 2) • D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0
    rw [one_smul]
    exact hD

private lemma list_repr_mem_cut_space {V : Type u} (G : SimpleGraph V)
    {D : EdgeSpace G}
    (hD : ∃ cuts : List (Set G.edgeSet),
      (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
        D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0) :
    D ∈ cut_space G := by
  classical
  rcases hD with ⟨cuts, hcuts, rfl⟩
  induction cuts with
  | nil =>
      simp [cut_space]
  | cons F Fs ih =>
      have hF : edge_indicator G F ∈ cut_space G := by
        rcases hcuts F (by simp) with hcut | hEmpty
        · exact edge_indicator_mem_cut_space_of_isCut G hcut
        · subst F
          simpa [edge_indicator_empty] using (Submodule.zero_mem (cut_space G))
      have hFs : (Fs.foldr (fun F acc => edge_indicator G F + acc) 0) ∈ cut_space G := by
        apply ih
        intro E hE
        exact hcuts E (by simp [hE])
      simpa using Submodule.add_mem (cut_space G) hF hFs

private lemma cut_space_list_repr {V : Type u} (G : SimpleGraph V) (D : EdgeSpace G) :
    D ∈ cut_space G ↔
      ∃ cuts : List (Set G.edgeSet),
        (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
          D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0 := by
  constructor
  · intro hD
    change D ∈ Submodule.span (ZMod 2) {F : EdgeSpace G | ∃ A : Set V, F = cut_vector G A} at hD
    induction hD using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨A, rfl⟩
        exact cut_vector_list_repr G A
    | zero =>
        exact list_repr_zero G
    | add x y _ _ hx hy =>
        exact list_repr_add G hx hy
    | smul a x _ hx =>
        exact list_repr_smul G a hx
  · exact list_repr_mem_cut_space G

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

private lemma mk_mem_atomic_cut_iff {V : Type u} (G : SimpleGraph V)
    {x y v : V} {he : s(x, y) ∈ G.edgeSet} :
    (⟨s(x, y), he⟩ : G.edgeSet) ∈ atomic_cut G v ↔ v = x ∨ v = y := by
  rw [atomic_cut_eq_incidence]
  change v ∈ (s(x, y) : Sym2 V) ↔ v = x ∨ v = y
  simp [Sym2.mem_iff]

private lemma cut_vector_eq_sum_atomic {V : Type u} (G : SimpleGraph V) [Fintype V]
    (A : Set V) :
    cut_vector G A =
      (vertsIn A).sum (fun v => edge_indicator G (atomic_cut G v)) := by
  classical
  ext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using he
      have hne : x ≠ y := hxy.ne
      by_cases hx : x ∈ A
      · by_cases hy : y ∈ A
        · have hnotcut : ¬ (⟨s(x, y), he⟩ : (SimpleGraph.edgeSet G)) ∈ cut_edges G A := by
            rintro ⟨a, ha, b, hb, hab⟩
            have hbA : b ∈ A := by
              rcases (Sym2.eq_iff.mp hab) with h | h
              · exact h.2 ▸ hy
              · exact h.1 ▸ hx
            exact hb hbA
          have hsum :
              ((vertsIn A).sum fun v =>
                  edge_indicator G (atomic_cut G v)
                (⟨s(x, y), he⟩ : G.edgeSet)) = 0 := by
            let S := vertsIn A
            let f : V → ZMod 2 := fun v =>
              edge_indicator G (atomic_cut G v) (⟨s(x, y), he⟩ : G.edgeSet)
            have hxS : x ∈ S := mem_vertsIn.mpr hx
            have hyS : y ∈ S.erase x := by
              simp [S, mem_vertsIn.mpr hy, hne.symm]
            have hrest : ((S.erase x).erase y).sum f = 0 := by
              rw [Finset.sum_eq_zero]
              intro v hvS
              have hvx : v ≠ x := by
                exact fun h => by
                  subst v
                  simpa using hvS
              have hvy : v ≠ y := by
                exact fun h => by
                  subst v
                  simpa using hvS
              have hnot : (⟨s(x, y), he⟩ : G.edgeSet) ∉ atomic_cut G v := by
                rw [mk_mem_atomic_cut_iff]
                exact not_or.mpr ⟨hvx, hvy⟩
              simp [f, edge_indicator, hnot]
            have hxmem : (⟨s(x, y), he⟩ : G.edgeSet) ∈ atomic_cut G x := by
              rw [mk_mem_atomic_cut_iff]
              exact Or.inl rfl
            have hymem : (⟨s(x, y), he⟩ : G.edgeSet) ∈ atomic_cut G y := by
              rw [mk_mem_atomic_cut_iff]
              exact Or.inr rfl
            calc
              (vertsIn A).sum (fun v =>
                  edge_indicator G (atomic_cut G v) (⟨s(x, y), he⟩ : G.edgeSet))
                  = f x + (S.erase x).sum f := by
                    rw [← Finset.add_sum_erase S f hxS]
              _ = f x + (f y + ((S.erase x).erase y).sum f) := by
                    rw [← Finset.add_sum_erase (S.erase x) f hyS]
              _ = f x + (f y + 0) := by
                    rw [hrest]
              _ = 0 := by
                    simp [f, hxmem, hymem, edge_indicator]
                    decide
          rw [Finset.sum_apply]
          rw [hsum]
          simp [cut_vector, edge_indicator, hnotcut]
        · have hcut : (⟨s(x, y), he⟩ : G.edgeSet) ∈ cut_edges G A :=
            ⟨x, hx, y, by simpa using hy, rfl⟩
          have hsum :
              ((vertsIn A).sum fun v =>
                  edge_indicator G (atomic_cut G v)
                (⟨s(x, y), he⟩ : G.edgeSet)) = 1 := by
            rw [Finset.sum_eq_single x]
            · have hmem : (⟨s(x, y), he⟩ : G.edgeSet) ∈ atomic_cut G x := by
                rw [mk_mem_atomic_cut_iff]
                exact Or.inl rfl
              simp [edge_indicator, hmem]
            · intro v hvA hvx
              have hv : v ∈ A := mem_vertsIn.mp hvA
              have hnot : (⟨s(x, y), he⟩ : G.edgeSet) ∉ atomic_cut G v := by
                rw [mk_mem_atomic_cut_iff]
                exact not_or.mpr ⟨hvx, fun hvy => hy (hvy ▸ hv)⟩
              simp [edge_indicator, hnot]
            · intro hxnot
              exact (hxnot (mem_vertsIn.mpr hx)).elim
          rw [Finset.sum_apply]
          rw [hsum]
          simp [cut_vector, edge_indicator, hcut]
      · by_cases hy : y ∈ A
        · have hcut : (⟨s(x, y), he⟩ : G.edgeSet) ∈ cut_edges G A :=
            ⟨y, hy, x, by simpa using hx, Sym2.eq_swap⟩
          have hsum :
              ((vertsIn A).sum fun v =>
                  edge_indicator G (atomic_cut G v)
                (⟨s(x, y), he⟩ : G.edgeSet)) = 1 := by
            rw [Finset.sum_eq_single y]
            · have hmem : (⟨s(x, y), he⟩ : G.edgeSet) ∈ atomic_cut G y := by
                rw [mk_mem_atomic_cut_iff]
                exact Or.inr rfl
              simp [edge_indicator, hmem]
            · intro v hvA hvy
              have hv : v ∈ A := mem_vertsIn.mp hvA
              have hnot : (⟨s(x, y), he⟩ : G.edgeSet) ∉ atomic_cut G v := by
                rw [mk_mem_atomic_cut_iff]
                exact not_or.mpr ⟨fun hvx => hx (hvx ▸ hv), hvy⟩
              simp [edge_indicator, hnot]
            · intro hynot
              exact (hynot (mem_vertsIn.mpr hy)).elim
          rw [Finset.sum_apply]
          rw [hsum]
          simp [cut_vector, edge_indicator, hcut]
        · have hnotcut : ¬ (⟨s(x, y), he⟩ : G.edgeSet) ∈ cut_edges G A := by
            rintro ⟨a, ha, b, hb, hab⟩
            rcases (Sym2.eq_iff.mp hab) with h | h
            · exact hx (h.1 ▸ ha)
            · exact hy (h.2 ▸ ha)
          have hsum :
              ((vertsIn A).sum fun v =>
                  edge_indicator G (atomic_cut G v)
                (⟨s(x, y), he⟩ : G.edgeSet)) = 0 := by
            rw [Finset.sum_eq_zero]
            intro v hvA
            have hnot : (⟨s(x, y), he⟩ : G.edgeSet) ∉ atomic_cut G v := by
              rw [mk_mem_atomic_cut_iff]
              exact not_or.mpr
                ⟨fun hvx => hx (hvx ▸ mem_vertsIn.mp hvA),
                  fun hvy => hy (hvy ▸ mem_vertsIn.mp hvA)⟩
            simp [edge_indicator, hnot]
          rw [Finset.sum_apply]
          rw [hsum]
          simp [cut_vector, edge_indicator, hnotcut]

private lemma cut_space_eq_atomic_span {V : Type u} (G : SimpleGraph V) [Fintype V] :
    cut_space G =
      Submodule.span (ZMod 2)
        {D : EdgeSpace G | ∃ v : V, D = edge_indicator G (atomic_cut G v)} := by
  classical
  apply le_antisymm
  · rw [cut_space]
    apply Submodule.span_le.mpr
    rintro D ⟨A, rfl⟩
    rw [cut_vector_eq_sum_atomic G A]
    exact Submodule.sum_mem _ fun v _ =>
      Submodule.subset_span
        (show edge_indicator G (atomic_cut G v) ∈
          {D : EdgeSpace G | ∃ v : V, D = edge_indicator G (atomic_cut G v)} from
          ⟨v, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro D ⟨v, rfl⟩
    simpa [cut_vector, atomic_cut] using cut_vector_mem_cut_space G ({v} : Set V)

/--
Diestel, Proposition 1.9.2.
Together with the empty set, cuts form the cut space; this space is
generated by atomic cuts.
-/
theorem proposition_1_9_2 {V : Type u} (G : SimpleGraph V) [Fintype V] :
  (∀ D : EdgeSpace G,
    D ∈ cut_space G ↔
      ∃ cuts : List (Set G.edgeSet),
        (∀ F ∈ cuts, IsCut G F ∨ F = ∅) ∧
          D = cuts.foldr (fun F acc => edge_indicator G F + acc) 0) ∧
    cut_space G =
      Submodule.span (ZMod 2) {D : EdgeSpace G | ∃ v : V, D = edge_indicator G (atomic_cut G v)} := by
  exact ⟨cut_space_list_repr G, cut_space_eq_atomic_span G⟩

end Chapter01
end Diestel
