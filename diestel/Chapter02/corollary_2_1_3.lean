import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

private lemma regular_positive_hall {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ}
    (hreg : G.IsRegularOfDegree k) (hk : 1 ≤ k) :
    ∀ S : Set V, S.ncard ≤ (⋃ v ∈ S, G.neighborSet v).ncard := by
  classical
  intro S
  let N : Set V := ⋃ v ∈ S, G.neighborSet v
  let s : Finset V := S.toFinset
  let t : Finset V := N.toFinset
  have hs_card : S.ncard = s.card := by
    simpa [s] using (Set.ncard_eq_toFinset_card S)
  have ht_card : N.ncard = t.card := by
    simpa [t] using (Set.ncard_eq_toFinset_card N)
  have hleft : ∀ a ∈ s, k ≤ (Finset.bipartiteAbove G.Adj t a).card := by
    intro a ha
    have hsubset : G.neighborFinset a ⊆ Finset.bipartiteAbove G.Adj t a := by
      intro b hb
      rw [Finset.mem_bipartiteAbove]
      have hAdj : G.Adj a b := (G.mem_neighborFinset a b).mp hb
      have hbN : b ∈ N := by
        refine Set.mem_iUnion.mpr ⟨a, ?_⟩
        refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
        · simpa [s] using ha
        · simpa [SimpleGraph.mem_neighborSet] using hAdj
      exact ⟨by simpa [t] using hbN, hAdj⟩
    calc
      k = G.degree a := (hreg.degree_eq a).symm
      _ = (G.neighborFinset a).card := (G.card_neighborFinset_eq_degree a).symm
      _ ≤ (Finset.bipartiteAbove G.Adj t a).card := Finset.card_le_card hsubset
  have hright : ∀ b ∈ t, (Finset.bipartiteBelow G.Adj s b).card ≤ k := by
    intro b hb
    have hsubset : Finset.bipartiteBelow G.Adj s b ⊆ G.neighborFinset b := by
      intro a ha
      rw [Finset.mem_bipartiteBelow] at ha
      exact (G.mem_neighborFinset b a).mpr ha.2.symm
    calc
      (Finset.bipartiteBelow G.Adj s b).card ≤ (G.neighborFinset b).card :=
        Finset.card_le_card hsubset
      _ = G.degree b := G.card_neighborFinset_eq_degree b
      _ = k := hreg.degree_eq b
  have hmul : s.card * k ≤ t.card * k :=
    Finset.card_mul_le_card_mul G.Adj hleft hright
  have hcard : s.card ≤ t.card :=
    Nat.le_of_mul_le_mul_right hmul (Nat.succ_le_iff.mp hk)
  rwa [hs_card, ht_card]

/--
Diestel, Corollary 2.1.3.
Natural-language statement:
Every finite positive-degree regular bipartite graph has a 1-factor.
-/
theorem corollary_2_1_3 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (A B : Set V) (k : ℕ) :
  G.IsBipartiteWith A B →
    G.IsRegularOfDegree k →
      1 ≤ k →
        ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  intro hAB hreg hk
  exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hAB
    (regular_positive_hall G hreg hk)

end Chapter02
end Diestel
