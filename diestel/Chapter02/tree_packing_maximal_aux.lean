import Chapter02.lemma_2_4_5
import Chapter02.multigraph_spanning_tree_on_aux
import Chapter02.multigraph_spanning_tree_aux
import Chapter02.tree_packing_glue_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v w

namespace MultiGraph

variable {V : Type u} {E : Type v} {ι : Type w}

/-- A family of spanning trees whose edge union is inclusion-maximal among such families. -/
def IsMaximalTreeFamilyUnion (G : MultiGraph V E) (T : ι → Set E) : Prop :=
  G.FamilySpanningTrees T ∧
    ∀ T' : ι → Set E, G.FamilySpanningTrees T' → ¬ FamilyEdgeSet T ⊂ FamilyEdgeSet T'

lemma exists_maximalTreeFamilyUnion_of_connected
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    (hG : G.Connected) :
    ∃ T : Fin k → Set E, G.IsMaximalTreeFamilyUnion T := by
  classical
  obtain ⟨F, hF⟩ := exists_isSpanningTree_of_connected (G := G) hG
  let fams : Set (Fin k → Set E) := {T | G.FamilySpanningTrees T}
  have hfamsFinite : fams.Finite := Set.toFinite fams
  have hfamsNonempty : fams.Nonempty := by
    exact ⟨fun _ : Fin k => F, by intro _; exact hF⟩
  obtain ⟨T, hTmax⟩ :=
    hfamsFinite.exists_maximalFor (fun T : Fin k → Set E => (FamilyEdgeSet T).ncard)
      fams hfamsNonempty
  refine ⟨T, hTmax.1, ?_⟩
  intro T' hT' hssub
  have hlt : (FamilyEdgeSet T).ncard < (FamilyEdgeSet T').ncard :=
    Set.ncard_lt_ncard hssub
  have hle : (FamilyEdgeSet T').ncard ≤ (FamilyEdgeSet T).ncard :=
    hTmax.2 hT' hlt.le
  exact (not_lt_of_ge hle) hlt

lemma startsExchangeChain_of_not_mem_familyEdgeSet
    {G : MultiGraph V E} {T : ι → Set E} {e : E}
    (he : e ∉ FamilyEdgeSet T) :
    G.StartsExchangeChain T e := by
  exact ⟨e, he, Relation.ReflTransGen.refl⟩

lemma not_edgeInAtLeastTwoTrees_of_startsExchangeChain_of_maximal
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} {e : E}
    (hLoopless : G.Loopless) (hMax : G.IsMaximalTreeFamilyUnion T)
    (hStart : G.StartsExchangeChain T e) :
    ¬ EdgeInAtLeastTwoTrees T e := by
  intro hTwo
  rcases lemma_2_4_5 (G := G) (T := T) (e := e)
      hLoopless hMax.1 hStart hTwo with
    ⟨T', hT', hssub⟩
  exact hMax.2 T' hT' hssub

lemma not_edgeInAtLeastTwoTrees_of_not_mem_familyEdgeSet_of_maximal
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} {e : E}
    (hLoopless : G.Loopless) (hMax : G.IsMaximalTreeFamilyUnion T)
    (he : e ∉ FamilyEdgeSet T) :
    ¬ EdgeInAtLeastTwoTrees T e :=
  not_edgeInAtLeastTwoTrees_of_startsExchangeChain_of_maximal
    (G := G) (T := T) (e := e) hLoopless hMax
    (startsExchangeChain_of_not_mem_familyEdgeSet (G := G) (T := T) he)

/-- The edge set `D` in Diestel's proof of Theorem 2.4.4. -/
def ExchangeChainEdgeSet (G : MultiGraph V E) (T : ι → Set E) : Set E :=
  {e | e ∈ G.edgeSet ∧ G.StartsExchangeChain T e}

lemma mem_exchangeChainEdgeSet_of_not_mem_familyEdgeSet
    {G : MultiGraph V E} {T : ι → Set E} {e : E}
    (heG : e ∈ G.edgeSet) (heT : e ∉ FamilyEdgeSet T) :
    e ∈ G.ExchangeChainEdgeSet T :=
  ⟨heG, startsExchangeChain_of_not_mem_familyEdgeSet (G := G) (T := T) heT⟩

lemma not_edgeInAtLeastTwoTrees_of_mem_exchangeChainEdgeSet_of_maximal
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} {e : E}
    (hLoopless : G.Loopless) (hMax : G.IsMaximalTreeFamilyUnion T)
    (heD : e ∈ G.ExchangeChainEdgeSet T) :
    ¬ EdgeInAtLeastTwoTrees T e :=
  not_edgeInAtLeastTwoTrees_of_startsExchangeChain_of_maximal
    (G := G) (T := T) (e := e) hLoopless hMax heD.2

lemma mem_exchangeChainEdgeSet_of_exchangeStep_of_mem_exchangeChainEdgeSet
    {G : MultiGraph V E} {T : ι → Set E} {e f : E}
    (heG : e ∈ G.edgeSet) (hef : G.IsExchangeStep T e f)
    (hfD : f ∈ G.ExchangeChainEdgeSet T) :
    e ∈ G.ExchangeChainEdgeSet T := by
  rcases hfD with ⟨_hfG, g, hg, hfg⟩
  exact ⟨heG, g, hg, Relation.ReflTransGen.head hef hfg⟩

lemma mem_exchangeChainEdgeSet_of_mem_shadow_path
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hFam : G.FamilySpanningTrees T) {i : Fin k}
    {e f : E} (heD : e ∈ G.ExchangeChainEdgeSet T)
    (heTi : e ∉ T i) (hfTi : f ∈ T i)
    {x y : G.vertexSet} (hlinke : G.IsLink e x.1 y.1)
    {p : (TreeShadow.Shadow G (T i)).Walk x y} (hp : p.IsPath)
    (hfp : TreeShadow.edgeSym2 (G := G) f ((hFam i).2.1 hfTi) ∈ p.edges) :
    f ∈ G.ExchangeChainEdgeSet T := by
  have hReplace :
      G.IsSpanningTree (((T i) ∪ {e}) \ {f}) :=
    TreeShadow.isSpanningTree_union_singleton_diff_of_mem_shadow_path
      (G := G) (F := T i) (e := e) (f := f)
      hLoopless (hFam i) heD.1 heTi hfTi hlinke hp hfp
  have hStep : G.IsExchangeStep T f e :=
    ⟨i, hFam i, hfTi, heTi, hReplace⟩
  exact mem_exchangeChainEdgeSet_of_exchangeStep_of_mem_exchangeChainEdgeSet
    (G := G) (T := T) (e := f) (f := e)
    ((hFam i).2.1 hfTi) hStep heD

/-- The simple graph `(V,D)` from the proof of Theorem 2.4.4. -/
abbrev ExchangeChainSubgraph (G : MultiGraph V E) (T : ι → Set E) :
    SimpleGraph G.vertexSet :=
  (G.edgeSubgraph (G.ExchangeChainEdgeSet T)).induce G.vertexSet

/-- The vertex set in `V` corresponding to one connected component of `(V,D)`. -/
def exchangeComponentVertexSet (G : MultiGraph V E) (T : ι → Set E)
    (C : (G.ExchangeChainSubgraph T).ConnectedComponent) : Set V :=
  {v | ∃ hv : v ∈ G.vertexSet, (⟨v, hv⟩ : G.vertexSet) ∈ C.supp}

/-- The partition `P` of `V` into vertex sets of components of `(V,D)`. -/
noncomputable def exchangeComponentPartition (G : MultiGraph V E) [Finite V]
    (T : ι → Set E) : Finset (Set V) :=
  by
    classical
    letI : Fintype (G.ExchangeChainSubgraph T).ConnectedComponent := Fintype.ofFinite _
    exact Finset.univ.image (exchangeComponentVertexSet G T)

lemma exchangeComponentVertexSet_mem_partition
    (G : MultiGraph V E) [Finite V] (T : ι → Set E)
    (C : (G.ExchangeChainSubgraph T).ConnectedComponent) :
    exchangeComponentVertexSet G T C ∈ G.exchangeComponentPartition T := by
  classical
  letI : Fintype (G.ExchangeChainSubgraph T).ConnectedComponent := Fintype.ofFinite _
  rw [exchangeComponentPartition]
  exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩

lemma exchangeComponentPartition_isVertexPartition
    (G : MultiGraph V E) [Finite V] (T : ι → Set E) :
    IsVertexPartitionOf G.vertexSet (G.exchangeComponentPartition T) := by
  classical
  letI : Fintype (G.ExchangeChainSubgraph T).ConnectedComponent := Fintype.ofFinite _
  let H : SimpleGraph G.vertexSet := G.ExchangeChainSubgraph T
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    rw [exchangeComponentPartition] at hU
    rcases Finset.mem_image.mp hU with ⟨C, _hC, rfl⟩
    constructor
    · rcases C.nonempty_supp with ⟨x, hxC⟩
      exact ⟨x.1, x.2, hxC⟩
    · intro v hv
      exact hv.1
  · intro U hU W hW hUW
    rw [Set.disjoint_left]
    intro z hzU hzW
    rw [exchangeComponentPartition] at hU hW
    rcases Finset.mem_image.mp hU with ⟨C, _hC, rfl⟩
    rcases Finset.mem_image.mp hW with ⟨D, _hD, rfl⟩
    rcases hzU with ⟨hzG, hzC⟩
    rcases hzW with ⟨hzG', hzD'⟩
    let zC : G.vertexSet := ⟨z, hzG⟩
    let zD : G.vertexSet := ⟨z, hzG'⟩
    have hzD : zC ∈ D.supp := by
      have hzd_eq : zD = zC := Subtype.ext rfl
      simpa [zC, zD, hzd_eq] using hzD'
    have hCD : C = D :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (G := H) (v := zC) hzC hzD
    exact hUW (by simp [exchangeComponentVertexSet, hCD])
  · intro v hv
    let x : G.vertexSet := ⟨v, hv⟩
    let C : H.ConnectedComponent := H.connectedComponentMk x
    refine ⟨exchangeComponentVertexSet G T C,
      exchangeComponentVertexSet_mem_partition (G := G) (T := T) C, ?_⟩
    exact ⟨hv, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

lemma exchangeChainSubgraph_adj_of_mem_exchangeChainEdgeSet
    {G : MultiGraph V E} {T : ι → Set E} (hLoopless : G.Loopless)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T)
    {x y : V} (hlink : G.IsLink e x y) :
    (G.ExchangeChainSubgraph T).Adj
      (⟨x, hlink.left_mem⟩ : G.vertexSet)
      (⟨y, hlink.right_mem⟩ : G.vertexSet) := by
  refine ⟨?_, e, heD, heD.1, hlink⟩
  intro hxy
  have hxyv : x = y := by
    simpa using hxy
  exact hLoopless heD.1 x (by
    change G.IsLink e x x
    simpa [hxyv] using hlink)

lemma exchangeComponent_eq_of_mem_exchangeChainEdgeSet_isLink
    {G : MultiGraph V E} {T : ι → Set E} (hLoopless : G.Loopless)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T)
    {x y : V} (hlink : G.IsLink e x y) :
    (G.ExchangeChainSubgraph T).connectedComponentMk
        (⟨x, hlink.left_mem⟩ : G.vertexSet) =
      (G.ExchangeChainSubgraph T).connectedComponentMk
        (⟨y, hlink.right_mem⟩ : G.vertexSet) := by
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (exchangeChainSubgraph_adj_of_mem_exchangeChainEdgeSet
      (G := G) (T := T) hLoopless heD hlink)

lemma not_isCrossEdge_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
    {G : MultiGraph V E} [Finite V] {T : ι → Set E}
    (hLoopless : G.Loopless) {e : E}
    (heD : e ∈ G.ExchangeChainEdgeSet T) :
    ¬ G.IsCrossEdge (G.exchangeComponentPartition T) e := by
  intro heCross
  rcases heCross with
    ⟨_heG, x, y, hlink, U, hU, W, hW, hUW, hxU, hyW⟩
  classical
  let H : SimpleGraph G.vertexSet := G.ExchangeChainSubgraph T
  rw [exchangeComponentPartition] at hU hW
  rcases Finset.mem_image.mp hU with ⟨C, _hC, hUeq⟩
  rcases Finset.mem_image.mp hW with ⟨D, _hD, hWeq⟩
  subst U
  subst W
  rcases hxU with ⟨hxG, hxC⟩
  rcases hyW with ⟨hyG, hyD⟩
  let x' : G.vertexSet := ⟨x, hxG⟩
  let y' : G.vertexSet := ⟨y, hyG⟩
  have hxC' : x' ∈ C.supp := hxC
  have hyD' : y' ∈ D.supp := hyD
  have hxyComp :
      H.connectedComponentMk x' = H.connectedComponentMk y' := by
    have hx_eq : x' = (⟨x, hlink.left_mem⟩ : G.vertexSet) := Subtype.ext rfl
    have hy_eq : y' = (⟨y, hlink.right_mem⟩ : G.vertexSet) := Subtype.ext rfl
    simpa [H, x', y', hx_eq, hy_eq] using
      exchangeComponent_eq_of_mem_exchangeChainEdgeSet_isLink
        (G := G) (T := T) hLoopless heD hlink
  have hxD' : x' ∈ D.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact hxyComp.trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff D y').mp hyD')
  have hCD : C = D :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (G := H) (v := x') hxC' hxD'
  exact hUW (by simp [exchangeComponentVertexSet, hCD])

lemma right_mem_of_left_mem_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
    {G : MultiGraph V E} [Finite V] {T : ι → Set E}
    (hLoopless : G.Loopless) {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T)
    {x y : V} (hlink : G.IsLink e x y) (hxU : x ∈ U) :
    y ∈ U := by
  classical
  let H : SimpleGraph G.vertexSet := G.ExchangeChainSubgraph T
  rw [exchangeComponentPartition] at hU
  rcases Finset.mem_image.mp hU with ⟨C, _hC, rfl⟩
  rcases hxU with ⟨hxG, hxC⟩
  refine ⟨hlink.right_mem, ?_⟩
  have hAdj :
      H.Adj (⟨x, hlink.left_mem⟩ : G.vertexSet)
        (⟨y, hlink.right_mem⟩ : G.vertexSet) :=
    exchangeChainSubgraph_adj_of_mem_exchangeChainEdgeSet
      (G := G) (T := T) hLoopless heD hlink
  have hxC' :
      (⟨x, hlink.left_mem⟩ : G.vertexSet) ∈ C.supp := by
    have hx_eq : (⟨x, hlink.left_mem⟩ : G.vertexSet) =
        (⟨x, hxG⟩ : G.vertexSet) := Subtype.ext rfl
    simpa [hx_eq] using hxC
  exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hAdj).mp hxC'

lemma left_mem_of_right_mem_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
    {G : MultiGraph V E} [Finite V] {T : ι → Set E}
    (hLoopless : G.Loopless) {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T)
    {x y : V} (hlink : G.IsLink e x y) (hyU : y ∈ U) :
    x ∈ U :=
  right_mem_of_left_mem_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
    (G := G) (T := T) hLoopless hU heD hlink.symm hyU

/-- The subgraph `S_j` induced on a `D`-component by the `j`th chosen tree. -/
def exchangeInternalTrace (G : MultiGraph V E) (T : ι → Set E)
    (i : ι) (U : Set V) : Set E :=
  {e | e ∈ T i ∧ e ∈ G.ExchangeChainEdgeSet T ∧ e ∈ G.EdgeSetInside U}

lemma exchangeInternalTrace_subset_tree
    {G : MultiGraph V E} {T : ι → Set E} {i : ι} {U : Set V} :
    G.exchangeInternalTrace T i U ⊆ T i := by
  intro e he
  exact he.1

lemma exchangeInternalTrace_subset_inside
    {G : MultiGraph V E} {T : ι → Set E} {i : ι} {U : Set V} :
    G.exchangeInternalTrace T i U ⊆ G.EdgeSetInside U := by
  intro e he
  exact he.2.2

lemma exchangeInternalTrace_edgeDisjoint_of_maximal
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T) (U : Set V) :
    EdgeDisjointFamily (fun i : Fin k => G.exchangeInternalTrace T i U) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro e hei hej
  have heD : e ∈ G.ExchangeChainEdgeSet T := hei.2.1
  exact not_edgeInAtLeastTwoTrees_of_mem_exchangeChainEdgeSet_of_maximal
    (G := G) (T := T) hLoopless hMax heD
    ⟨i, j, hij, hei.1, hej.1⟩

lemma exchangeInternalTrace_adj_of_shadow_adj_mem_path
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hFam : G.FamilySpanningTrees T) {i : Fin k} {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T) (heTi : e ∉ T i)
    {x y : G.vertexSet} (hlinke : G.IsLink e x.1 y.1)
    {p : (TreeShadow.Shadow G (T i)).Walk x y} (hp : p.IsPath)
    {a b : G.vertexSet} (hab : (TreeShadow.Shadow G (T i)).Adj a b)
    (habEdge : s(a, b) ∈ p.edges) (haU : a.1 ∈ U) :
    ∃ hbU : b.1 ∈ U,
      ((G.edgeSubgraph (G.exchangeInternalTrace T i U)).induce U).Adj
        (⟨a.1, haU⟩ : U) (⟨b.1, hbU⟩ : U) := by
  rcases hab with ⟨hne, f, hfTi, hfG, hlinkf⟩
  have hsym :
      TreeShadow.edgeSym2 (G := G) f ((hFam i).2.1 hfTi) = s(a, b) :=
    TreeShadow.edgeSym2_eq_of_isLink
      (G := G) (e := f) ((hFam i).2.1 hfTi) hlinkf
  have hfD : f ∈ G.ExchangeChainEdgeSet T :=
    mem_exchangeChainEdgeSet_of_mem_shadow_path
      (G := G) (T := T) hLoopless hFam heD heTi hfTi hlinke hp
      (by simpa [hsym] using habEdge)
  have hbU : b.1 ∈ U :=
    right_mem_of_left_mem_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
      (G := G) (T := T) hLoopless hU hfD hlinkf haU
  refine ⟨hbU, ?_⟩
  have hinside : f ∈ G.EdgeSetInside U := by
    refine ⟨hfG, ?_⟩
    intro z hz
    rcases hz.eq_or_eq_of_isLink hlinkf with rfl | rfl
    · exact haU
    · exact hbU
  refine ⟨?_, f, ⟨hfTi, hfD, hinside⟩, hfG, hlinkf⟩
  intro hEq
  have hval : a.1 = b.1 := by
    simpa using hEq
  exact hne hval

lemma exchangeInternalTrace_reachable_of_shadow_walk_edges_subset_path
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hFam : G.FamilySpanningTrees T) {i : Fin k} {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T) (heTi : e ∉ T i)
    {x₀ y₀ : G.vertexSet} (hlinke : G.IsLink e x₀.1 y₀.1)
    {p₀ : (TreeShadow.Shadow G (T i)).Walk x₀ y₀} (hp₀ : p₀.IsPath)
    {x y : G.vertexSet} (w : (TreeShadow.Shadow G (T i)).Walk x y)
    (hwEdges : ∀ q : Sym2 G.vertexSet, q ∈ w.edges → q ∈ p₀.edges)
    (hxU : x.1 ∈ U) :
    ∃ hyU : y.1 ∈ U,
      ((G.edgeSubgraph (G.exchangeInternalTrace T i U)).induce U).Reachable
        (⟨x.1, hxU⟩ : U) (⟨y.1, hyU⟩ : U) := by
  induction w with
  | nil =>
      exact ⟨hxU, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab w ih =>
      have hhead : s(a, b) ∈ p₀.edges :=
        hwEdges s(a, b) (by simp [SimpleGraph.Walk.edges_cons])
      rcases exchangeInternalTrace_adj_of_shadow_adj_mem_path
          (G := G) (T := T) hLoopless hFam hU heD heTi hlinke hp₀ hab hhead hxU with
        ⟨hbU, hAdj⟩
      have htailEdges : ∀ q : Sym2 G.vertexSet, q ∈ w.edges → q ∈ p₀.edges := by
        intro q hq
        exact hwEdges q (by simp [SimpleGraph.Walk.edges_cons, hq])
      rcases ih htailEdges hbU with ⟨hyU, hreachTail⟩
      exact ⟨hyU, (SimpleGraph.Adj.reachable hAdj).trans hreachTail⟩

lemma exchangeInternalTrace_reachable_of_mem_exchangeChainEdgeSet
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hFam : G.FamilySpanningTrees T) {i : Fin k} {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T)
    {e : E} (heD : e ∈ G.ExchangeChainEdgeSet T)
    {x y : V} (hlinke : G.IsLink e x y) (hxU : x ∈ U) :
    ∃ hyU : y ∈ U,
      ((G.edgeSubgraph (G.exchangeInternalTrace T i U)).induce U).Reachable
        (⟨x, hxU⟩ : U) (⟨y, hyU⟩ : U) := by
  by_cases heTi : e ∈ T i
  · have hyU : y ∈ U :=
      right_mem_of_left_mem_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
        (G := G) (T := T) hLoopless hU heD hlinke hxU
    have hinside : e ∈ G.EdgeSetInside U := by
      refine ⟨heD.1, ?_⟩
      intro z hz
      rcases hz.eq_or_eq_of_isLink hlinke with rfl | rfl
      · exact hxU
      · exact hyU
    have hAdj :
        ((G.edgeSubgraph (G.exchangeInternalTrace T i U)).induce U).Adj
          (⟨x, hxU⟩ : U) (⟨y, hyU⟩ : U) := by
      refine ⟨?_, e, ⟨heTi, heD, hinside⟩, heD.1, hlinke⟩
      intro hxy
      have hval : x = y := by simpa using hxy
      exact hLoopless heD.1 x (by
        change G.IsLink e x x
        simpa [hval] using hlinke)
    exact ⟨hyU, SimpleGraph.Adj.reachable hAdj⟩
  · let xG : G.vertexSet := ⟨x, hlinke.left_mem⟩
    let yG : G.vertexSet := ⟨y, hlinke.right_mem⟩
    have hvNonempty : G.vertexSet.Nonempty := ⟨x, hlinke.left_mem⟩
    have hconn :
        (TreeShadow.Shadow G (T i)).Connected :=
      (TreeShadow.isSpanningTree_connected_card_of_vertex_nonempty
        (G := G) (F := T i) (hFam i) hvNonempty).1
    rcases hconn.exists_isPath xG yG with ⟨p, hp⟩
    have hedgeSubset : ∀ q : Sym2 G.vertexSet, q ∈ p.edges → q ∈ p.edges :=
      fun q hq => hq
    simpa [xG, yG] using
      exchangeInternalTrace_reachable_of_shadow_walk_edges_subset_path
        (G := G) (T := T) hLoopless hFam hU heD heTi hlinke
        (p₀ := p) hp p hedgeSubset hxU

lemma exchangeInternalTrace_reachable_of_exchangeChainSubgraph_walk
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hFam : G.FamilySpanningTrees T) {i : Fin k} {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T)
    {x y : G.vertexSet} (w : (G.ExchangeChainSubgraph T).Walk x y)
    (hxU : x.1 ∈ U) :
    ∃ hyU : y.1 ∈ U,
      ((G.edgeSubgraph (G.exchangeInternalTrace T i U)).induce U).Reachable
        (⟨x.1, hxU⟩ : U) (⟨y.1, hyU⟩ : U) := by
  induction w with
  | nil =>
      exact ⟨hxU, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab w ih =>
      rcases hab with ⟨_hne, e, heD, _heG, hlink⟩
      rcases exchangeInternalTrace_reachable_of_mem_exchangeChainEdgeSet
          (G := G) (T := T) hLoopless hFam (i := i) hU heD hlink hxU with
        ⟨hbU, hreachHead⟩
      rcases ih hbU with ⟨hyU, hreachTail⟩
      exact ⟨hyU, hreachHead.trans hreachTail⟩

lemma exchangeInternalTrace_connected
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hFam : G.FamilySpanningTrees T) {i : Fin k} {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T) :
    ((G.edgeSubgraph (G.exchangeInternalTrace T i U)).induce U).Connected := by
  classical
  let H : SimpleGraph G.vertexSet := G.ExchangeChainSubgraph T
  rw [exchangeComponentPartition] at hU
  rcases Finset.mem_image.mp hU with ⟨C, _hC, hUeq⟩
  subst U
  refine { preconnected := fun x y => ?_, nonempty := ?_ }
  rcases x.2 with ⟨hxG, hxC⟩
  rcases y.2 with ⟨hyG, hyC⟩
  let xG : G.vertexSet := ⟨x.1, hxG⟩
  let yG : G.vertexSet := ⟨y.1, hyG⟩
  have hcomp :
      H.connectedComponentMk xG = H.connectedComponentMk yG := by
    have hxComp : H.connectedComponentMk xG = C := by
      simpa [xG] using (SimpleGraph.ConnectedComponent.mem_supp_iff C xG).mp hxC
    have hyComp : H.connectedComponentMk yG = C := by
      simpa [yG] using (SimpleGraph.ConnectedComponent.mem_supp_iff C yG).mp hyC
    exact hxComp.trans hyComp.symm
  have hreachH : H.Reachable xG yG :=
    SimpleGraph.ConnectedComponent.exact hcomp
  rcases hreachH with ⟨w⟩
  rcases exchangeInternalTrace_reachable_of_exchangeChainSubgraph_walk
      (G := G) (T := T) hLoopless hFam (i := i)
      (U := exchangeComponentVertexSet G T C)
      (exchangeComponentVertexSet_mem_partition (G := G) (T := T) C)
      w x.2 with
    ⟨hyU, hreach⟩
  simpa [xG, yG] using hreach
  · rcases C.nonempty_supp with ⟨x, hxC⟩
    exact ⟨⟨x.1, x.2, hxC⟩⟩

lemma exchangeInternalTrace_isSpanningTreeOn
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T) {i : Fin k} {U : Set V}
    (hU : U ∈ G.exchangeComponentPartition T) :
    G.IsSpanningTreeOn U (G.exchangeInternalTrace T i U) := by
  classical
  have hP := exchangeComponentPartition_isVertexPartition (G := G) (T := T)
  exact TreeShadow.isSpanningTreeOn_of_connected_subset_spanningTree
    (G := G) (F := T i) (A := G.exchangeInternalTrace T i U) (U := U)
    hLoopless (hMax.1 i) (hP.1 U hU).2
    (exchangeInternalTrace_subset_tree (G := G) (T := T) (i := i) (U := U))
    (exchangeInternalTrace_subset_inside (G := G) (T := T) (i := i) (U := U))
    (exchangeInternalTrace_connected
      (G := G) (T := T) hLoopless hMax.1 (i := i) hU)

lemma exchangeComponentPartition_hasKEdgeDisjointSpanningTreesOn
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T) :
    ∀ U ∈ G.exchangeComponentPartition T,
      G.HasKEdgeDisjointSpanningTreesOn U k := by
  intro U hU
  refine ⟨fun i : Fin k => G.exchangeInternalTrace T i U, ?_, ?_⟩
  · intro i
    exact exchangeInternalTrace_isSpanningTreeOn
      (G := G) (T := T) hLoopless hMax (i := i) hU
  · exact exchangeInternalTrace_edgeDisjoint_of_maximal
      (G := G) (T := T) hLoopless hMax U

/-- The trace of one selected spanning tree on the quotient by the `D`-components. -/
def exchangeQuotientTrace (G : MultiGraph V E) [Finite V]
    (T : ι → Set E) (i : ι) :
    Set (G.CrossEdge (G.exchangeComponentPartition T)) :=
  {e | e.1 ∈ T i}

lemma exchangeQuotientTrace_covers_crossEdges
    {G : MultiGraph V E} [Finite V] {T : ι → Set E}
    (hLoopless : G.Loopless) :
    ∀ e : G.CrossEdge (G.exchangeComponentPartition T),
      ∃ i : ι, e ∈ G.exchangeQuotientTrace T i := by
  intro e
  by_cases heT : e.1 ∈ FamilyEdgeSet T
  · rcases heT with ⟨i, hei⟩
    exact ⟨i, hei⟩
  · have heD : e.1 ∈ G.ExchangeChainEdgeSet T :=
      mem_exchangeChainEdgeSet_of_not_mem_familyEdgeSet
        (G := G) (T := T) e.2.1 heT
    exact False.elim
      (not_isCrossEdge_exchangeComponentPartition_of_mem_exchangeChainEdgeSet
        (G := G) (T := T) hLoopless heD e.2)

lemma exchangeQuotientTrace_connected
    {G : MultiGraph V E} [Finite V] {k : ℕ}
    {T : Fin k → Set E} (hFam : G.FamilySpanningTrees T)
    (hPne : (G.exchangeComponentPartition T).Nonempty) (i : Fin k) :
    (G.quotientEdgeSubgraph (G.exchangeComponentPartition T)
      (G.exchangeQuotientTrace T i)).Connected := by
  classical
  have hP := exchangeComponentPartition_isVertexPartition (G := G) (T := T)
  simpa [exchangeQuotientTrace] using
    quotientEdgeSubgraph_connected_of_spanningTree
      (G := G) (F := T i) (P := G.exchangeComponentPartition T)
      hP hPne (hFam i)

lemma exchangeQuotientTrace_ncard_le
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T)
    (hPne : (G.exchangeComponentPartition T).Nonempty) (i : Fin k) :
    (G.exchangeQuotientTrace T i).ncard ≤
      (G.exchangeComponentPartition T).card - 1 := by
  classical
  let P : Finset (Set V) := G.exchangeComponentPartition T
  let A : {U : Set V // U ∈ P} → Set E :=
    fun U => G.exchangeInternalTrace T i U.1
  let Q : Set (G.CrossEdge P) := G.exchangeQuotientTrace T i
  let I : Set E := ⋃ U : {U : Set V // U ∈ P}, A U
  let L : Set E := G.liftQuotientEdgeSet Q
  have hP : IsVertexPartitionOf G.vertexSet P := by
    simpa [P] using exchangeComponentPartition_isVertexPartition (G := G) (T := T)
  have hVne : G.vertexSet.Nonempty := by
    rcases hPne with ⟨U, hU⟩
    rcases (hP.1 U (by simpa [P] using hU)).1 with ⟨v, hvU⟩
    exact ⟨v, (hP.1 U (by simpa [P] using hU)).2 hvU⟩
  have hA_tree :
      ∀ U : {U : Set V // U ∈ P}, G.IsSpanningTreeOn U.1 (A U) := by
    intro U
    exact exchangeInternalTrace_isSpanningTreeOn
      (G := G) (T := T) hLoopless hMax (i := i) (by simpa [P] using U.2)
  have hpairA : Pairwise fun U W => Disjoint (A U) (A W) := by
    intro U W hUW
    rw [Set.disjoint_left]
    intro e heU heW
    have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U).2.2.1 heU
    have heWinside : e ∈ G.EdgeSetInside W.1 := (hA_tree W).2.2.1 heW
    exact Set.disjoint_left.mp
      (edgeSetInside_disjoint_of_ne_partitionClass
        (G := G) (P := P) hP U.2 W.2 (fun h => hUW (Subtype.ext h)))
      heUinside heWinside
  have hIcard : I.ncard = ∑ U : {U : Set V // U ∈ P}, (A U).ncard := by
    change (⋃ U : {U : Set V // U ∈ P}, A U).ncard =
      ∑ U : {U : Set V // U ∈ P}, (A U).ncard
    rw [Set.ncard_iUnion_of_finite]
    · exact finsum_eq_finset_sum_of_support_subset _ (by intro U _hU; simp)
    · intro U
      exact (hA_tree U).2.1
    · exact hpairA
  have hAcard : ∀ U : {U : Set V // U ∈ P}, (A U).ncard + 1 = U.1.ncard := by
    intro U
    exact isSpanningTreeOn_ncard_add_one_eq_of_nonempty
      (G := G) (U := U.1) (F := A U) (hA_tree U) (hP.1 U.1 U.2).1
  have hSubtypeCard : Fintype.card {U : Set V // U ∈ P} = P.card := by
    calc
      Fintype.card {U : Set V // U ∈ P} = Nat.card {U : Set V // U ∈ P} :=
        (Nat.card_eq_fintype_card).symm
      _ = P.card := partitionSubtype_natCard_eq (V := V) P
  have hsumA_add :
      (∑ U : {U : Set V // U ∈ P}, (A U).ncard) + P.card =
        G.vertexSet.ncard := by
    calc
      (∑ U : {U : Set V // U ∈ P}, (A U).ncard) + P.card =
          (∑ U : {U : Set V // U ∈ P}, (A U).ncard) +
            Fintype.card {U : Set V // U ∈ P} := by rw [hSubtypeCard]
      _ = ∑ U : {U : Set V // U ∈ P}, ((A U).ncard + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ U : {U : Set V // U ∈ P}, U.1.ncard := by
        apply Finset.sum_congr rfl
        intro U _hU
        exact hAcard U
      _ = G.vertexSet.ncard :=
        isVertexPartitionOf_subtype_sum_ncard_eq (X := G.vertexSet) hP
  have hILdisj : Disjoint I L := by
    rw [Set.disjoint_left]
    intro e heI heL
    rcases Set.mem_iUnion.mp heI with ⟨U, heU⟩
    have heUinside : e ∈ G.EdgeSetInside U.1 := (hA_tree U).2.2.1 heU
    exact Set.disjoint_left.mp
      (liftQuotientEdgeSet_disjoint_edgeSetInside
        (G := G) (P := P) hP U.2 (Q := Q)).symm
      heUinside heL
  have hUnionSubset : I ∪ L ⊆ T i := by
    intro e he
    rcases he with heI | heL
    · rcases Set.mem_iUnion.mp heI with ⟨U, heU⟩
      exact heU.1
    · rcases heL with ⟨q, hqQ, rfl⟩
      exact hqQ
  have hUnionCardLe : (I ∪ L).ncard ≤ (T i).ncard :=
    Set.ncard_le_ncard hUnionSubset
  have hUnionCard : (I ∪ L).ncard = I.ncard + L.ncard := by
    exact Set.ncard_union_eq hILdisj
  have hLcard : L.ncard = Q.ncard := by
    simpa [L] using liftQuotientEdgeSet_ncard (G := G) Q
  have hTcard : (T i).ncard + 1 = G.vertexSet.ncard :=
    (TreeShadow.isSpanningTree_connected_card_of_vertex_nonempty
      (G := G) (F := T i) (hMax.1 i) hVne).2
  have hQle : Q.ncard ≤ P.card - 1 := by
    rw [hUnionCard, hIcard, hLcard] at hUnionCardLe
    omega
  simpa [P, Q] using hQle

lemma exchangeQuotientTrace_isQuotientSpanningTree
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T)
    (hPne : (G.exchangeComponentPartition T).Nonempty) (i : Fin k) :
    G.IsQuotientSpanningTree (G.exchangeComponentPartition T)
      (G.exchangeQuotientTrace T i) := by
  classical
  let P : Finset (Set V) := G.exchangeComponentPartition T
  let Q : Set (G.CrossEdge P) := G.exchangeQuotientTrace T i
  have hP : IsVertexPartitionOf G.vertexSet P := by
    simpa [P] using exchangeComponentPartition_isVertexPartition (G := G) (T := T)
  have hLowerNat :
      P.card - 1 ≤ Nat.card {e : G.CrossEdge P | e.1 ∈ T i} :=
    partition_card_sub_one_le_selected_crossEdges_of_spanningTree
      (G := G) (F := T i) (P := P) hP (hMax.1 i)
  let R : Set (G.CrossEdge P) := {e : G.CrossEdge P | e.1 ∈ T i}
  have hQR : Q = R := by
    rfl
  have hLowerR : P.card - 1 ≤ R.ncard := by
    calc
      P.card - 1 ≤ Nat.card R := by
        simpa [R] using hLowerNat
      _ = R.ncard := TreeShadow.natCard_subtype_eq_ncard (F := R)
  have hLower : P.card - 1 ≤ Q.ncard := by
    simpa [hQR]
      using hLowerR
  have hUpper : Q.ncard ≤ P.card - 1 := by
    simpa [P, Q] using
      exchangeQuotientTrace_ncard_le
        (G := G) (T := T) hLoopless hMax hPne i
  have hPpos : 0 < P.card := by
    exact Finset.card_pos.mpr (by simpa [P] using hPne)
  refine ⟨Set.toFinite Q, Or.inr ?_⟩
  constructor
  · simpa [P, Q] using
      exchangeQuotientTrace_connected
        (G := G) (T := T) hMax.1 hPne i
  · have hQcard : Q.ncard = P.card - 1 := le_antisymm hUpper hLower
    have hcard : Q.ncard + 1 = P.card := by
      omega
    simpa [P, Q] using hcard

lemma exchangeComponentPartition_quotientEdgesCovered
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T)
    (hPne : (G.exchangeComponentPartition T).Nonempty) :
    G.QuotientEdgesCoveredByKSpanningTrees (G.exchangeComponentPartition T) k := by
  refine ⟨fun i : Fin k => G.exchangeQuotientTrace T i, ?_, ?_⟩
  · intro i
    exact exchangeQuotientTrace_isQuotientSpanningTree
      (G := G) (T := T) hLoopless hMax hPne i
  · exact exchangeQuotientTrace_covers_crossEdges
      (G := G) (T := T) hLoopless

lemma packingCoveringPartition_exchangeComponentPartition
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    {T : Fin k → Set E} (hLoopless : G.Loopless)
    (hMax : G.IsMaximalTreeFamilyUnion T)
    (hPne : (G.exchangeComponentPartition T).Nonempty) :
    G.PackingCoveringPartition (G.exchangeComponentPartition T) k := by
  exact ⟨exchangeComponentPartition_isVertexPartition (G := G) (T := T),
    exchangeComponentPartition_hasKEdgeDisjointSpanningTreesOn
      (G := G) (T := T) hLoopless hMax,
    exchangeComponentPartition_quotientEdgesCovered
      (G := G) (T := T) hLoopless hMax hPne⟩

lemma exists_packingCoveringPartition_of_connected
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    (hLoopless : G.Loopless) (hG : G.Connected) :
    ∃ P : Finset (Set V), G.PackingCoveringPartition P k := by
  classical
  rcases exists_maximalTreeFamilyUnion_of_connected (G := G) (k := k) hG with
    ⟨T, hMax⟩
  have hPne : (G.exchangeComponentPartition T).Nonempty := by
    rcases hG.nonempty with ⟨v⟩
    rcases (exchangeComponentPartition_isVertexPartition (G := G) (T := T)).2.2
        v.1 v.2 with
      ⟨U, hU, _hvU⟩
    exact ⟨U, hU⟩
  exact ⟨G.exchangeComponentPartition T,
    packingCoveringPartition_exchangeComponentPartition
      (G := G) (T := T) hLoopless hMax hPne⟩

end MultiGraph

end Chapter02
end Diestel
