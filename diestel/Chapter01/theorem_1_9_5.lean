import Chapter01.cut_cycle_space_dimension
import Chapter01.lemma_1_9_3

set_option linter.all false

namespace Diestel
namespace Chapter01

open scoped BigOperators

universe u

private lemma mapLe_edges_eq {V : Type u} {G H : SimpleGraph V} (h : G ≤ H)
    {x y : V} (p : G.Walk x y) :
    (p.mapLe h).edges = p.edges := by
  simpa [SimpleGraph.Walk.mapLe, SimpleGraph.Hom.ofLE] using
    (SimpleGraph.Walk.edges_map (SimpleGraph.Hom.ofLE h) p)

private lemma mapLe_edgeSet_subset_source {V : Type u} {G H : SimpleGraph V}
    (h : G ≤ H) {x y : V} (p : G.Walk x y) :
    ∀ e : Sym2 V, e ∈ (p.mapLe h).edgeSet → e ∈ G.edgeSet := by
  intro e he
  rw [SimpleGraph.Walk.mem_edgeSet] at he
  rw [mapLe_edges_eq h p] at he
  exact p.edges_subset_edgeSet he

private lemma delete_edge_endpoints_not_reachable {V : Type u} [DecidableEq V]
    {T : SimpleGraph V} {x y : V} (hT : T.IsTree) (hxy : T.Adj x y) :
    ¬ (T.deleteEdges {s(x, y)}).Reachable x y := by
  intro hreach
  rcases hreach with ⟨q⟩
  let H := T.deleteEdges {s(x, y)}
  have hHleT : H ≤ T := by
    intro a b hab
    exact (SimpleGraph.deleteEdges_adj.mp hab).1
  let qT : T.Walk x y := q.mapLe hHleT
  let direct : T.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
  have hdirect_path : direct.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    simp [SimpleGraph.Walk.support_nil, hxy.ne]
  have hq_path : qT.bypass.IsPath := SimpleGraph.Walk.bypass_isPath qT
  obtain ⟨p, hp, hpuniq⟩ := hT.existsUnique_path x y
  have hdirect_eq : direct = qT.bypass := by
    exact (hpuniq direct hdirect_path).trans (hpuniq qT.bypass hq_path).symm
  have hdirect_edge : s(x, y) ∈ direct.edges := by
    simp [direct, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
  have hqT_edge_bypass : s(x, y) ∈ qT.bypass.edges := by
    simpa [hdirect_eq] using hdirect_edge
  have hqT_edge : s(x, y) ∈ qT.edges :=
    SimpleGraph.Walk.edges_bypass_subset qT hqT_edge_bypass
  have hq_edge : s(x, y) ∈ q.edges := by
    simpa [qT, H, mapLe_edges_eq hHleT q] using hqT_edge
  have hHedge : s(x, y) ∈ H.edgeSet := q.edges_subset_edgeSet hq_edge
  have hHadj : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp hHedge
  exact (SimpleGraph.deleteEdges_adj.mp hHadj).2 (by simp)

private lemma exists_fundamental_cycle_of_chord {V : Type u}
    (G T : SimpleGraph V) [DecidableEq V]
    (hST : IsSpanningTree G T) :
    ∀ e : Sym2 V, e ∈ G.edgeSet → e ∉ T.edgeSet →
      ∃ a : V, ∃ c : G.Walk a a, IsFundamentalCycle G T e c := by
  intro e
  induction e using Sym2.inductionOn with
  | hf x y =>
      intro heG heT
      have hTG : T ≤ G := hST.1
      have hTtree : T.IsTree := hST.2
      have hxyG : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp heG
      obtain ⟨p, hp_path, _hpuniq⟩ := hTtree.existsUnique_path y x
      let pG : G.Walk y x := p.mapLe hTG
      have hpG_path : pG.IsPath := hp_path.mapLe hTG
      have hnot_edges : s(x, y) ∉ pG.edges := by
        intro hs
        have hsT : s(x, y) ∈ T.edgeSet := by
          have hs_source : s(x, y) ∈ p.edges := by
            simpa [pG, mapLe_edges_eq hTG p] using hs
          exact p.edges_subset_edgeSet hs_source
        exact heT hsT
      let c : G.Walk x x := SimpleGraph.Walk.cons hxyG pG
      refine ⟨x, c, ?_⟩
      refine ⟨hST, ⟨heG, heT⟩, ?_, ?_, ?_⟩
      · exact (SimpleGraph.Walk.cons_isCycle_iff pG hxyG).mpr ⟨hpG_path, hnot_edges⟩
      · simp [c, SimpleGraph.Walk.edgeSet_cons]
      · intro f hf
        have hf' : f ∈ insert s(x, y) pG.edgeSet := by
          simpa [c, SimpleGraph.Walk.edgeSet_cons] using hf
        rcases Set.mem_insert_iff.mp hf' with rfl | hf
        · exact Or.inl rfl
        · exact Or.inr (mapLe_edgeSet_subset_source hTG p f hf)

private lemma reachable_step {V : Type u} {H : SimpleGraph V} {x a b : V}
    (hxa : H.Reachable x a) (hab : H.Adj a b) : H.Reachable x b := by
  rcases hxa with ⟨p⟩
  exact ⟨p.append (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil)⟩

private lemma fundamental_tree_cut {V : Type u} [DecidableEq V]
    (G T : SimpleGraph V) [Fintype V]
    (hST : IsSpanningTree G T) :
    ∀ f : G.edgeSet, (f : Sym2 V) ∈ T.edgeSet →
      ∃ D : Set G.edgeSet,
        IsBond G D ∧ f ∈ D ∧
          ∀ e : G.edgeSet, e ∈ D → e = f ∨ (e : Sym2 V) ∉ T.edgeSet := by
  intro f hfT
  rcases hST with ⟨hTG, hTtree⟩
  rcases f with ⟨ef, hefG⟩
  induction ef using Sym2.inductionOn with
  | hf x y =>
      have hxyT : T.Adj x y := (SimpleGraph.mem_edgeSet T).mp hfT
      let H := T.deleteEdges {s(x, y)}
      let A : Set V := {v | H.Reachable x v}
      have hxA : x ∈ A := by
        exact ⟨SimpleGraph.Walk.nil⟩
      have hyA : y ∉ A := by
        exact delete_edge_endpoints_not_reachable hTtree hxyT
      let D0 : Set G.edgeSet := cut_edges G A
      have hD0_cut : IsCut G D0 := by
        refine ⟨A, ⟨x, hxA⟩, ⟨y, hyA⟩, rfl⟩
      have hfD0 : (⟨s(x, y), hefG⟩ : G.edgeSet) ∈ D0 := by
        change (⟨s(x, y), hefG⟩ : G.edgeSet) ∈ cut_edges G A
        exact ⟨x, hxA, y, hyA, rfl⟩
      have hD0_tree :
          ∀ e : G.edgeSet, e ∈ D0 →
            e = (⟨s(x, y), hefG⟩ : G.edgeSet) ∨ (e : Sym2 V) ∉ T.edgeSet := by
        intro e heD0
        by_cases heT : (e : Sym2 V) ∈ T.edgeSet
        · left
          obtain ⟨ee, heeG⟩ := e
          induction ee using Sym2.inductionOn with
          | hf a b =>
              have habT : T.Adj a b := (SimpleGraph.mem_edgeSet T).mp heT
              have hcross :
                  (a ∈ A ∧ b ∉ A) ∨ (b ∈ A ∧ a ∉ A) := by
                rcases heD0 with ⟨u, huA, v, hvA, huv⟩
                rcases Sym2.eq_iff.mp huv with h | h
                · exact Or.inl ⟨by simpa [h.1] using huA, by simpa [h.2] using hvA⟩
                · exact Or.inr ⟨by simpa [h.2] using huA, by simpa [h.1] using hvA⟩
              have heq_sym : s(a, b) = s(x, y) := by
                by_contra hne
                have habH : H.Adj a b := by
                  exact (SimpleGraph.deleteEdges_adj).mpr
                    ⟨habT, by simpa [Set.mem_singleton_iff] using hne⟩
                rcases hcross with hcross | hcross
                · have hbA : b ∈ A := reachable_step hcross.1 habH
                  exact hcross.2 hbA
                · have haA : a ∈ A := reachable_step hcross.1 habH.symm
                  exact hcross.2 haA
              apply Subtype.ext
              exact heq_sym
        · exact Or.inr heT
      obtain ⟨bonds, hbonds, _hdisj, hD0_union⟩ := lemma_1_9_3 G D0 hD0_cut
      have hfD0_union :
          (⟨s(x, y), hefG⟩ : G.edgeSet) ∈ {e | ∃ B ∈ bonds, e ∈ B} := by
        rw [← hD0_union]
        exact hfD0
      rcases hfD0_union with ⟨B, hBbonds, hfB⟩
      refine ⟨B, hbonds B hBbonds, hfB, ?_⟩
      intro e heB
      have heD0 : e ∈ D0 := by
        rw [hD0_union]
        exact ⟨B, hBbonds, heB⟩
      exact hD0_tree e heD0

/--
Diestel, Theorem 1.9.5.
For a connected graph with spanning tree `T`, the fundamental cuts and
fundamental cycles with respect to `T` exist and give the usual dimensions.
-/
theorem theorem_1_9_5 {V : Type u} (G T : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet] :
  G.Connected →
    IsSpanningTree G T →
      (∀ e : Sym2 V, e ∈ G.edgeSet → e ∉ T.edgeSet →
        ∃ a : V, ∃ c : G.Walk a a, IsFundamentalCycle G T e c) ∧
        (∀ f : G.edgeSet, (f : Sym2 V) ∈ T.edgeSet →
          ∃ D : Set G.edgeSet,
            IsBond G D ∧ f ∈ D ∧
              ∀ e : G.edgeSet, e ∈ D → e = f ∨ (e : Sym2 V) ∉ T.edgeSet) ∧
          Module.finrank (ZMod 2) (cut_space G) = Fintype.card V - 1 ∧
            Module.finrank (ZMod 2) (cycle_space G) =
              G.edgeFinset.card + 1 - Fintype.card V := by
  intro hG hST
  refine ⟨exists_fundamental_cycle_of_chord G T hST, ?_⟩
  refine ⟨fundamental_tree_cut G T hST, ?_⟩
  exact ⟨cut_space_finrank_connected G hG, cycle_space_finrank_connected G hG⟩

end Chapter01
end Diestel
