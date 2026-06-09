import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma exists_lifted_edge_of_toSimple_adj {G : MultiGraph V E}
    {x y : G.vertexSet} (hxy : G.toSimpleGraph.Adj x y) :
    ∃ e : E, e ∈ G.edgeSet ∧ G.IsLink e x.1 y.1 := by
  rcases hxy with ⟨_hne, e, hlink⟩
  exact ⟨e, hlink.edge_mem, hlink⟩

lemma exists_lifted_edge_of_tree_edge {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    (q : T.edgeSet) :
    ∃ e : E, e ∈ G.edgeSet ∧
      ∃ x y : G.vertexSet, (q : Sym2 G.vertexSet) = s(x, y) ∧
        G.IsLink e x.1 y.1 := by
  rcases q with ⟨qval, hq⟩
  change ∃ e : E, e ∈ G.edgeSet ∧
      ∃ x y : G.vertexSet, qval = s(x, y) ∧ G.IsLink e x.1 y.1
  induction qval using Sym2.inductionOn with
  | hf x y =>
      have hxy : T.Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using hq
      rcases exists_lifted_edge_of_toSimple_adj (G := G) (hTG hxy) with
        ⟨e, heG, hlink⟩
      exact ⟨e, heG, x, y, rfl, hlink⟩

noncomputable def liftedTreeEdge {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    (q : T.edgeSet) : E :=
  Classical.choose (exists_lifted_edge_of_tree_edge (G := G) hTG q)

lemma liftedTreeEdge_mem {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    (q : T.edgeSet) :
    liftedTreeEdge (G := G) hTG q ∈ G.edgeSet :=
  (Classical.choose_spec (exists_lifted_edge_of_tree_edge (G := G) hTG q)).1

lemma liftedTreeEdge_spec {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph)
    (q : T.edgeSet) :
    ∃ x y : G.vertexSet, (q : Sym2 G.vertexSet) = s(x, y) ∧
      G.IsLink (liftedTreeEdge (G := G) hTG q) x.1 y.1 :=
  (Classical.choose_spec (exists_lifted_edge_of_tree_edge (G := G) hTG q)).2

lemma liftedTreeEdge_injective {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph) :
    Function.Injective (liftedTreeEdge (G := G) hTG) := by
  classical
  intro q r hqr
  obtain ⟨x, y, hqval, hqLink⟩ := liftedTreeEdge_spec (G := G) hTG q
  obtain ⟨x', y', hrval, hrLink⟩ := liftedTreeEdge_spec (G := G) hTG r
  have hrLink' : G.IsLink (liftedTreeEdge (G := G) hTG q) x'.1 y'.1 := by
    simpa [hqr] using hrLink
  apply Subtype.ext
  rw [hqval, hrval]
  rcases hqLink.eq_and_eq_or_eq_and_eq hrLink' with hsame | hswap
  · rcases hsame with ⟨hxx, hyy⟩
    have hx : x = x' := Subtype.ext hxx
    have hy : y = y' := Subtype.ext hyy
    subst x'
    subst y'
    rfl
  · rcases hswap with ⟨hxy, hyx⟩
    have hx : x = y' := Subtype.ext hxy
    have hy : y = x' := Subtype.ext hyx
    subst y'
    subst x'
    exact Sym2.eq_swap

noncomputable def liftedTreeEdgeSet {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph) : Set E :=
  Set.range (liftedTreeEdge (G := G) hTG)

lemma liftedTreeEdgeSet_finite {G : MultiGraph V E} [Finite E]
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph) :
    (liftedTreeEdgeSet (G := G) hTG).Finite :=
  Set.toFinite _

lemma liftedTreeEdgeSet_subset {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph) :
    liftedTreeEdgeSet (G := G) hTG ⊆ G.edgeSet := by
  rintro e ⟨q, rfl⟩
  exact liftedTreeEdge_mem (G := G) hTG q

lemma tree_le_edgeSubgraph_liftedTreeEdgeSet {G : MultiGraph V E}
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph) :
    T ≤ (G.edgeSubgraph (liftedTreeEdgeSet (G := G) hTG)).induce G.vertexSet := by
  classical
  intro x y hxy
  let q : T.edgeSet := ⟨s(x, y), by simpa [SimpleGraph.mem_edgeSet] using hxy⟩
  obtain ⟨a, b, hqval, hlink⟩ := liftedTreeEdge_spec (G := G) hTG q
  have hsym : s(a.1, b.1) = s(x.1, y.1) := by
    have hqval' : s(x, y) = s(a, b) := by
      simpa [q] using hqval
    rcases Sym2.eq_iff.mp hqval' with hsame | hswap
    · rcases hsame with ⟨hxa, hyb⟩
      subst a
      subst b
      rfl
    · rcases hswap with ⟨hxb, hya⟩
      subst b
      subst a
      exact Sym2.eq_swap
  have hlinkxy : G.IsLink (liftedTreeEdge (G := G) hTG q) x.1 y.1 := by
    exact (hlink.isLink_iff_sym2_eq).2 hsym
  exact ⟨(fun h => hxy.ne (Subtype.ext h)), liftedTreeEdge (G := G) hTG q, ⟨q, rfl⟩,
    liftedTreeEdge_mem (G := G) hTG q, hlinkxy⟩

lemma liftedTreeEdgeSet_isSpanningTree {G : MultiGraph V E} [Finite V] [Finite E]
    {T : SimpleGraph G.vertexSet} (hTG : T ≤ G.toSimpleGraph) (hT : T.IsTree) :
    G.IsSpanningTree (liftedTreeEdgeSet (G := G) hTG) := by
  classical
  refine ⟨liftedTreeEdgeSet_finite (G := G) hTG,
    liftedTreeEdgeSet_subset (G := G) hTG, ?_⟩
  right
  constructor
  · exact hT.connected.mono (tree_le_edgeSubgraph_liftedTreeEdgeSet (G := G) hTG)
  · have hRange :
        (liftedTreeEdgeSet (G := G) hTG).ncard = Nat.card T.edgeSet := by
      exact Set.ncard_range_of_injective (liftedTreeEdge_injective (G := G) hTG)
    have hTcard : Nat.card T.edgeSet + 1 = Nat.card G.vertexSet :=
      (SimpleGraph.isTree_iff_connected_and_card (G := T)).1 hT |>.2
    calc
      (liftedTreeEdgeSet (G := G) hTG).ncard + 1 = Nat.card T.edgeSet + 1 := by
        rw [hRange]
      _ = Nat.card G.vertexSet := hTcard
      _ = G.vertexSet.ncard := by simp

lemma edgeSubgraph_edgeSet_induce_eq_toSimpleGraph (G : MultiGraph V E) :
    (G.edgeSubgraph G.edgeSet).induce G.vertexSet = G.toSimpleGraph := by
  ext x y
  constructor
  · rintro ⟨hne, e, _heF, _heG, hlink⟩
    exact ⟨fun hxy => hne (congrArg Subtype.val hxy), e, hlink⟩
  · rintro ⟨hne, e, hlink⟩
    exact ⟨fun hxy => hne (Subtype.ext hxy), e, hlink.edge_mem, hlink.edge_mem, hlink⟩

lemma connected_of_isLEdgeConnected_pos {G : MultiGraph V E} {l : ℕ}
    (hconn : G.IsLEdgeConnected l) (hl : 0 < l) :
    G.Connected := by
  classical
  have h :=
    hconn (∅ : Set E) (Set.finite_empty) (by simp)
      (by simpa using hl)
  simpa [Connected, Set.diff_empty, edgeSubgraph_edgeSet_induce_eq_toSimpleGraph] using h

lemma exists_isSpanningTree_of_connected {G : MultiGraph V E} [Finite V] [Finite E]
    (hG : G.Connected) :
    ∃ F : Set E, G.IsSpanningTree F := by
  classical
  rcases hG.exists_isTree_le with ⟨T, hTG, hT⟩
  exact ⟨liftedTreeEdgeSet (G := G) hTG,
    liftedTreeEdgeSet_isSpanningTree (G := G) hTG hT⟩

lemma hasOneEdgeDisjointSpanningTree_of_connected {G : MultiGraph V E} [Finite V] [Finite E]
    (hG : G.Connected) :
    G.HasKEdgeDisjointSpanningTrees 1 := by
  classical
  rcases exists_isSpanningTree_of_connected (G := G) hG with ⟨F, hF⟩
  refine ⟨fun _ : Fin 1 => F, ?_, ?_⟩
  · intro _
    exact hF
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (hij rfl).elim

lemma hasOneEdgeDisjointSpanningTree_of_isLEdgeConnected_pos
    {G : MultiGraph V E} [Finite V] [Finite E] {l : ℕ}
    (hconn : G.IsLEdgeConnected l) (hl : 0 < l) :
    G.HasKEdgeDisjointSpanningTrees 1 :=
  hasOneEdgeDisjointSpanningTree_of_connected
    (G := G) (connected_of_isLEdgeConnected_pos (G := G) hconn hl)

end MultiGraph

end Chapter02
end Diestel
