import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

private lemma neighboursIn_eq_biUnion_of_subset_left {V : Type u} (G : SimpleGraph V)
    {A B S : Set V} (hAB : G.IsBipartiteWith A B) (hS : S ⊆ A) :
    neighboursIn G S B = ⋃ v ∈ S, G.neighborSet v := by
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    refine ⟨hy, ?_⟩
    rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxS, hyN⟩
    exact hAB.mem_of_mem_adj (hS hxS) (by simpa [SimpleGraph.mem_neighborSet] using hyN)

private lemma marriageCondition_of_matching {V : Type u} (G : SimpleGraph V)
    [Finite V] {A B : Set V} (hAB : G.IsBipartiteWith A B)
    (hmatch : HasMatchingOf G A) : MarriageCondition G A B := by
  classical
  rcases hmatch with ⟨M, hM, hAverts⟩
  intro S hS
  let mate (s : S) : V := Classical.choose (hM (hAverts (hS s.2)))
  have hmate_adj (s : S) : M.Adj s.1 (mate s) :=
    (Classical.choose_spec (hM (hAverts (hS s.2)))).1
  let f : S → neighboursIn G S B := fun s =>
    ⟨mate s, by
      have hGadj : G.Adj s.1 (mate s) := M.adj_sub (hmate_adj s)
      refine ⟨?_, hAB.mem_of_mem_adj (hS s.2) hGadj⟩
      refine Set.mem_iUnion.mpr ⟨s.1, ?_⟩
      refine Set.mem_iUnion.mpr ⟨s.2, ?_⟩
      simpa [SimpleGraph.mem_neighborSet] using hGadj⟩
  have hf_inj : Function.Injective f := by
    intro s t hst
    have hval : mate s = mate t := congr_arg Subtype.val hst
    have ht_adj : M.Adj t.1 (mate s) := by
      simpa [hval] using hmate_adj t
    exact Subtype.ext (hM.eq_of_adj_right (hmate_adj s) ht_adj)
  have hcard : Nat.card S ≤ Nat.card (neighboursIn G S B) :=
    Nat.card_le_card_of_injective f hf_inj
  simpa [Set.ncard] using hcard

/--
Diestel, Theorem 2.1.2 (Hall).
Natural-language statement:
A finite bipartite graph with bipartition `{A,B}` contains a matching of
`A` if and only if every subset of `A` has at least as many neighbours in
`B` as its own cardinality.
-/
theorem theorem_2_1_2 {V : Type u} (G : SimpleGraph V)
    [Finite V] (A B : Set V) :
  G.IsBipartiteWith A B →
    (HasMatchingOf G A ↔ MarriageCondition G A B) := by
  classical
  intro hAB
  constructor
  · exact marriageCondition_of_matching G hAB
  · intro hHall
    haveI : G.LocallyFinite := fun v => Fintype.ofFinite (G.neighborSet v)
    obtain ⟨M, hAverts, hM⟩ :=
      SimpleGraph.exists_isMatching_of_forall_ncard_le (G := G) (p₁ := A) (p₂ := B) hAB
        (fun S hS => by
          have hEq := neighboursIn_eq_biUnion_of_subset_left G hAB hS
          simpa [MarriageCondition, hEq] using hHall S hS)
    exact ⟨M, hM, hAverts⟩

end Chapter02
end Diestel
