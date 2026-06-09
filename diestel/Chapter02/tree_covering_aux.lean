import Chapter01.proposition_1_3_1
import Chapter02.cycle_packing_aux
import Chapter02.multigraph_spanning_tree_on_aux
import Chapter02.tree_packing_glue_aux
import Chapter02.theorem_2_4_4

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter02

universe u v

namespace SimpleGraph

variable {V : Type u}

lemma isAcyclic_edgeSet_natCard_le_card_sub_one
    {H : SimpleGraph V} [Finite V] [Nonempty V] (hH : H.IsAcyclic) :
    Nat.card H.edgeSet ≤ Nat.card V - 1 := by
  classical
  obtain ⟨T, hHT, hTmax⟩ :=
    SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
      (G := (⊤ : SimpleGraph V)) (H := H) (by simp) hH
  have hTmaxAcyclic : Maximal (fun K : SimpleGraph V => K.IsAcyclic) T := by
    refine ⟨hTmax.prop.2, ?_⟩
    intro K hK hTK
    exact hTmax.le_of_ge ⟨le_top, hK⟩ hTK
  have hTtree : T.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.mp hTmaxAcyclic
  have hcardT : Nat.card T.edgeSet + 1 = Nat.card V :=
    (SimpleGraph.isTree_iff_connected_and_card (G := T)).1 hTtree |>.2
  have hle : Nat.card H.edgeSet ≤ Nat.card T.edgeSet :=
    Nat.card_le_card_of_injective
      (fun e : H.edgeSet => (⟨e.1, SimpleGraph.edgeSet_mono hHT e.2⟩ : T.edgeSet))
      (by
        intro e f h
        exact Subtype.ext (congrArg (fun q : T.edgeSet => (q : Sym2 V)) h))
  have hVpos : 0 < Nat.card V := Nat.card_pos
  omega

end SimpleGraph

namespace MultiGraph

variable {V : Type u} {E : Type v}

namespace TreeCovering

def componentVertexSet (G : MultiGraph V E)
    (C : G.toSimpleGraph.ConnectedComponent) : Set V :=
  {v | ∃ hv : v ∈ G.vertexSet, (⟨v, hv⟩ : G.vertexSet) ∈ C.supp}

lemma componentVertexSet_subset (G : MultiGraph V E)
    (C : G.toSimpleGraph.ConnectedComponent) :
    componentVertexSet G C ⊆ G.vertexSet := by
  rintro v ⟨hv, _hC⟩
  exact hv

lemma induce_loopless {G : MultiGraph V E} (hLoopless : G.Loopless) (U : Set V) :
    Loopless (G.induce U) := by
  intro e he x hloop
  change (G.induce U).IsLink e x x at hloop
  rw [Graph.induce_isLink] at hloop
  exact hLoopless hloop.1.edge_mem x hloop.1

lemma inducedEdgeCount_induce_le
    {G : MultiGraph V E} [Finite E] (U W : Set V) :
    inducedEdgeCount (G.induce U) W ≤ G.inducedEdgeCount W := by
  classical
  let φ :
      {e : E // e ∈ EdgeSetInside (G.induce U) W} →
        {e : E // e ∈ G.EdgeSetInside W} := fun e =>
    ⟨e.1, by
      have heInd := e.2
      rcases heInd.1 with ⟨x, y, hlink, hxU, hyU⟩
      refine ⟨hlink.edge_mem, ?_⟩
      intro z hz
      have hzInd : (G.induce U).Inc e.1 z := by
        rcases hz.eq_or_eq_of_isLink hlink with rfl | rfl
        · exact ⟨y, by
            rw [Graph.induce_isLink]
            exact ⟨hlink, hxU, hyU⟩⟩
        · exact ⟨x, by
            rw [Graph.induce_isLink]
            exact ⟨hlink.symm, hyU, hxU⟩⟩
      exact heInd.2 z hzInd⟩
  exact Nat.card_le_card_of_injective φ (by
    intro e f hef
    exact Subtype.ext
      (congrArg (fun q : {e : E // e ∈ G.EdgeSetInside W} => (q : E)) hef))

lemma induced_component_connected
    (G : MultiGraph V E) (C : G.toSimpleGraph.ConnectedComponent) :
    Connected (G.induce (componentVertexSet G C)) := by
  classical
  let U : Set V := componentVertexSet G C
  let H : MultiGraph V E := G.induce U
  change H.toSimpleGraph.Connected
  let φ : C.toSimpleGraph →g H.toSimpleGraph := {
    toFun := fun x =>
      ⟨x.1.1, by
        change x.1.1 ∈ H.vertexSet
        exact ⟨x.1.2, x.2⟩⟩
    map_rel' := by
      intro x y hxy
      have hGadj : G.toSimpleGraph.Adj x.1 y.1 := by
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hxy
      rcases hGadj with ⟨hne, e, hlink⟩
      refine ⟨?_, e, ?_⟩
      · intro h
        exact hne (Subtype.ext (by
          exact congrArg (fun z : H.vertexSet => (z : V)) h))
      · change H.IsLink e x.1.1 y.1.1
        rw [Graph.induce_isLink]
        exact ⟨hlink, ⟨x.1.2, x.2⟩, ⟨y.1.2, y.2⟩⟩ }
  have hsurj : Function.Surjective φ := by
    intro z
    have hzU : z.1 ∈ U := by
      simpa [H] using z.2
    rcases hzU with ⟨hzG, hzC⟩
    refine ⟨⟨⟨z.1, hzG⟩, hzC⟩, ?_⟩
    exact Subtype.ext rfl
  exact (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C).map φ hsurj

lemma cycle_support_component_eq
    {G : MultiGraph V E} (C : G.CycleIn) {r v : V}
    (hr : r ∈ C.support) (hv : v ∈ C.support) :
    G.toSimpleGraph.connectedComponentMk
        (⟨v, C.support_subset_vertexSet hv⟩ : G.vertexSet) =
      G.toSimpleGraph.connectedComponentMk
        (⟨r, C.support_subset_vertexSet hr⟩ : G.vertexSet) := by
  classical
  let H : SimpleGraph C.support := (G.edgeSubgraph C.edgeSupport).induce C.support
  let φ : H →g G.toSimpleGraph := {
    toFun := fun x => ⟨x.1, C.support_subset_vertexSet x.2⟩
    map_rel' := by
      intro x y hxy
      rcases hxy with ⟨hne, e, _heC, _heG, hlink⟩
      refine ⟨?_, e, hlink⟩
      intro h
      exact hne (by
        exact congrArg (fun z : G.vertexSet => (z : V)) h) }
  have hreachH : H.Reachable (⟨v, hv⟩ : C.support) (⟨r, hr⟩ : C.support) :=
    C.connected.preconnected _ _
  have hreachG :
      G.toSimpleGraph.Reachable
        (⟨v, C.support_subset_vertexSet hv⟩ : G.vertexSet)
        (⟨r, C.support_subset_vertexSet hr⟩ : G.vertexSet) :=
    hreachH.map φ
  exact SimpleGraph.ConnectedComponent.sound hreachG

def cycleIn_of_induce {G : MultiGraph V E} {U : Set V}
    (C : G.CycleIn) (hCU : C.edgeSupport ⊆ (G.induce U).edgeSet) :
    CycleIn (G.induce U) where
  support := C.support
  edgeSupport := C.edgeSupport
  edgeSupport_finite := C.edgeSupport_finite
  edges_inside := by
    intro e heC
    refine ⟨hCU heC, ?_⟩
    intro v hv
    exact (C.edges_inside heC).2 v (by
      rcases hv with ⟨w, hlink⟩
      exact ⟨w, hlink.1⟩)
  support_nonempty := C.support_nonempty
  connected := by
    rcases C.connected with ⟨hpre⟩
    refine ⟨?_⟩
    intro x y
    exact (hpre x y).mono fun a b hab => by
      rcases hab with ⟨hne, e, heC, heG, hlink⟩
      have heU := hCU heC
      rcases heU with ⟨u, v, hlinkUV, huU, hvU⟩
      have haU : a.1 ∈ U := by
        change (Function.Embedding.subtype (fun x : V => x ∈ C.support)) a ∈ U
        rcases hlink.eq_and_eq_or_eq_and_eq hlinkUV with h | h
        · exact h.1 ▸ huU
        · exact h.1 ▸ hvU
      have hbU : b.1 ∈ U := by
        change (Function.Embedding.subtype (fun x : V => x ∈ C.support)) b ∈ U
        rcases hlink.eq_and_eq_or_eq_and_eq hlinkUV with h | h
        · exact h.2 ▸ hvU
        · exact h.2 ▸ huU
      refine ⟨hne, e, heC, ?_, ?_⟩
      · exact ⟨a.1, b.1, hlink, haU, hbU⟩
      · rw [Graph.induce_isLink]
        exact ⟨hlink, haU, hbU⟩
  degree_two := by
    intro v hv
    let ψ :
        {e : C.edgeSupport // (G.induce U).Inc e.1 v} ≃
          {e : C.edgeSupport // G.Inc e.1 v} := by
      refine
        { toFun := fun e =>
            ⟨e.1, by
              rcases e.2 with ⟨w, hlink⟩
              exact ⟨w, hlink.1⟩⟩
          invFun := fun e =>
            ⟨e.1, by
              have heU := hCU e.1.2
              rcases heU with ⟨x, y, hlinkXY, hxU, hyU⟩
              rcases e.2.eq_or_eq_of_isLink hlinkXY with hvx | hvy
              · subst x
                exact ⟨y, by
                  rw [Graph.induce_isLink]
                  exact ⟨hlinkXY, hxU, hyU⟩⟩
              · subst y
                exact ⟨x, by
                  rw [Graph.induce_isLink]
                  exact ⟨hlinkXY.symm, hyU, hxU⟩⟩⟩
          left_inv := by
            intro e
            rfl
          right_inv := by
            intro e
            rfl }
    rw [Nat.card_congr ψ]
    exact C.degree_two v hv

lemma CycleIn.edgeSupport_nonempty {G : MultiGraph V E} (C : G.CycleIn) :
    C.edgeSupport.Nonempty := by
  classical
  rcases C.support_nonempty with ⟨v, hv⟩
  have hcard := C.degree_two v hv
  have hpos : 0 < Nat.card {e : C.edgeSupport // G.Inc e.1 v} := by
    omega
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  haveI : Finite {e : C.edgeSupport // G.Inc e.1 v} := inferInstance
  rcases (Finite.card_pos_iff.mp hpos :
      Nonempty {e : C.edgeSupport // G.Inc e.1 v}) with ⟨e⟩
  exact ⟨e.1.1, e.1.2⟩

lemma edgeSym2InInduced_injective_of_forest
    {G : MultiGraph V E} {F A : Set E} {U : Set V}
    (hLoopless : G.Loopless) (hForest : G.IsForest F)
    (hAF : A ⊆ F) (hA : A ⊆ G.EdgeSetInside U) :
    Function.Injective (TreeShadow.edgeSym2InInduced (G := G) (A := A)
      hLoopless hA) := by
  classical
  intro e f hef
  by_cases heq : e.1 = f.1
  · exact Subtype.ext heq
  exfalso
  let φ := TreeShadow.edgeSym2InInduced (G := G) (A := A) hLoopless hA
  have hsym : (φ e : Sym2 U) = (φ f : Sym2 U) := congrArg Subtype.val hef
  have heG : e.1 ∈ G.edgeSet := (hA e.2).1
  have hfG : f.1 ∈ G.edgeSet := (hA f.2).1
  let ex := TreeShadow.edgeLeft (G := G) e.1 heG
  let ey := TreeShadow.edgeRight (G := G) e.1 heG
  let fx := TreeShadow.edgeLeft (G := G) f.1 hfG
  let fy := TreeShadow.edgeRight (G := G) f.1 hfG
  have heLink : G.IsLink e.1 ex ey :=
    TreeShadow.edgeLeft_isLink_edgeRight (G := G) e.1 heG
  have hfLink : G.IsLink f.1 fx fy :=
    TreeShadow.edgeLeft_isLink_edgeRight (G := G) f.1 hfG
  have hxU : ex ∈ U := (hA e.2).2 ex heLink.inc_left
  have hyU : ey ∈ U := (hA e.2).2 ey heLink.inc_right
  have hxFU : fx ∈ U := (hA f.2).2 fx hfLink.inc_left
  have hyFU : fy ∈ U := (hA f.2).2 fy hfLink.inc_right
  have hsym' : s((⟨ex, hxU⟩ : U), (⟨ey, hyU⟩ : U)) =
      s((⟨fx, hxFU⟩ : U), (⟨fy, hyFU⟩ : U)) := by
    simpa [φ, TreeShadow.edgeSym2InInduced, ex, ey, fx, fy] using hsym
  have he_ne : ex ≠ ey := by
    intro hxy
    exact hForest.2.2.1 e.1 (hAF e.2) ex (by simpa [ex, ey, hxy] using heLink)
  have hf_as_e : G.IsLink f.1 ex ey := by
    rcases Sym2.eq_iff.mp hsym' with hsame | hswap
    · rcases hsame with ⟨hxx, hyy⟩
      have hxx' : ex = fx := congrArg Subtype.val hxx
      have hyy' : ey = fy := congrArg Subtype.val hyy
      simpa [hxx', hyy'] using hfLink
    · rcases hswap with ⟨hxy, hyx⟩
      have hxy' : ex = fy := congrArg Subtype.val hxy
      have hyx' : ey = fx := congrArg Subtype.val hyx
      have hf' : G.IsLink f.1 fy fx := hfLink.symm
      simpa [hxy', hyx'] using hf'
  let C : G.CycleIn :=
    cycleOfParallelEdges (G := G) (e := e.1) (f := f.1)
      (by exact heq) he_ne heLink hf_as_e
  have hCsub : C.edgeSupport ⊆ F := by
    intro g hg
    change g ∈ ({e.1, f.1} : Set E) at hg
    rcases hg with rfl | rfl
    · exact hAF e.2
    · exact hAF f.2
  exact hForest.2.2.2 C hCsub

lemma induced_shadow_isAcyclic_of_forest
    {G : MultiGraph V E} [Finite E] {F A : Set E} {U : Set V}
    (hUsub : U ⊆ G.vertexSet) (hForest : G.IsForest F)
    (hAF : A ⊆ F) (hA : A ⊆ G.EdgeSetInside U) :
    ((G.edgeSubgraph A).induce U).IsAcyclic := by
  classical
  intro x p hp
  let M : MultiGraph V E := G.restrict A
  let inc : U ↪ M.vertexSet := {
    toFun := fun x =>
      ⟨x.1, by simpa [M] using hUsub x.2⟩
    inj' := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : M.vertexSet => z.1) hxy) }
  let hom : ((G.edgeSubgraph A).induce U) →g M.toSimpleGraph := {
    toFun := inc
    map_rel' := by
      intro a b hab
      rcases hab with ⟨hne, e, heA, _heG, hlink⟩
      refine ⟨?_, e, ?_⟩
      · intro h
        have hval : a.1 = b.1 := congrArg (fun z : M.vertexSet => (z : V)) h
        have habU :
            (Function.Embedding.subtype (fun x : V => x ∈ U)) a =
              (Function.Embedding.subtype (fun x : V => x ∈ U)) b :=
          hval
        exact hne habU
      · exact ⟨heA, hlink⟩ }
  have hpM : (p.map hom).IsCycle := hp.map inc.injective
  let CM : M.CycleIn := cycleOfSimpleCycle (G := M) hpM
  let C : G.CycleIn := cycleIn_of_subgraph (G := G) (H := M) Graph.restrict_le CM
  have hCsubA : C.edgeSupport ⊆ A := by
    intro e he
    have heM : e ∈ M.edgeSet := (CM.edges_inside he).1
    exact heM.2
  have hCsubF : C.edgeSupport ⊆ F := fun e he => hAF (hCsubA he)
  exact hForest.2.2.2 C hCsubF

lemma forest_inter_edgeSetInside_ncard_le
    {G : MultiGraph V E} [Finite V] [Finite E] {F : Set E} {U : Set V}
    (hLoopless : G.Loopless) (hUsub : U ⊆ G.vertexSet) (hUne : U.Nonempty)
    (hForest : G.IsForest F) :
    (F ∩ G.EdgeSetInside U).ncard ≤ U.ncard - 1 := by
  classical
  let A : Set E := F ∩ G.EdgeSetInside U
  let H : SimpleGraph U := (G.edgeSubgraph A).induce U
  have hAF : A ⊆ F := by
    intro e he
    exact he.1
  have hAinside : A ⊆ G.EdgeSetInside U := by
    intro e he
    exact he.2
  have hHacyclic : H.IsAcyclic :=
    induced_shadow_isAcyclic_of_forest
      (G := G) (F := F) (A := A) (U := U)
      hUsub hForest hAF hAinside
  haveI : Nonempty U := hUne.to_subtype
  have hHedge :
      Nat.card H.edgeSet ≤ Nat.card U - 1 :=
    Diestel.Chapter02.SimpleGraph.isAcyclic_edgeSet_natCard_le_card_sub_one
      (H := H) hHacyclic
  have hAedge :
      Nat.card A ≤ Nat.card H.edgeSet :=
    Nat.card_le_card_of_injective
      (TreeShadow.edgeSym2InInduced (G := G) (A := A) hLoopless hAinside)
      (edgeSym2InInduced_injective_of_forest
        (G := G) (F := F) (A := A) (U := U)
        hLoopless hForest hAF hAinside)
  calc
    (F ∩ G.EdgeSetInside U).ncard = A.ncard := rfl
    _ = Nat.card A := (TreeShadow.natCard_subtype_eq_ncard (F := A)).symm
    _ ≤ Nat.card H.edgeSet := hAedge
    _ ≤ Nat.card U - 1 := hHedge
    _ = U.ncard - 1 := by
      rw [TreeShadow.natCard_subtype_eq_ncard (F := U)]

noncomputable def coverIndex
    {G : MultiGraph V E} {n : ℕ} (T : Fin n → Set E)
    (hcover : G.EdgeCoveredByFamily T)
    (e : G.edgeSet) : Fin n :=
  Classical.choose (hcover e.1 e.2)

lemma coverIndex_mem
    {G : MultiGraph V E} {n : ℕ} (T : Fin n → Set E)
    (hcover : G.EdgeCoveredByFamily T)
    (e : G.edgeSet) :
    e.1 ∈ T (coverIndex (G := G) T hcover e) :=
  Classical.choose_spec (hcover e.1 e.2)

lemma canCoverEdgesByAtMostKTrees_inducedEdgeCount_bound
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    (hLoopless : G.Loopless)
    (hcover : G.CanCoverEdgesByAtMostKTrees k) :
    ∀ U : Set V, U ⊆ G.vertexSet → U.Nonempty →
      G.inducedEdgeCount U ≤ k * (U.ncard - 1) := by
  classical
  rintro U hUsub hUne
  rcases hcover with ⟨n, hnk, T, hForest, hCovered⟩
  let A : Set E := G.EdgeSetInside U
  let D : Type v := Sigma fun i : Fin n => {e : E // e ∈ T i ∩ A}
  let φ : A → D := fun e =>
    ⟨coverIndex (G := G) T hCovered ⟨e.1, e.2.1⟩,
      ⟨e.1, coverIndex_mem (G := G) T hCovered ⟨e.1, e.2.1⟩, e.2⟩⟩
  have hφinj : Function.Injective φ := by
    intro e f hef
    apply Subtype.ext
    exact congrArg (fun q : D => (q.2 : E)) hef
  have hA_le_D : Nat.card A ≤ Nat.card D :=
    Nat.card_le_card_of_injective φ hφinj
  have hDcard :
      Nat.card D = ∑ i : Fin n, Nat.card {e : E // e ∈ T i ∩ A} := by
    rw [Nat.card_sigma]
  have hterm : ∀ i : Fin n, Nat.card {e : E // e ∈ T i ∩ A} ≤ U.ncard - 1 := by
    intro i
    rw [TreeShadow.natCard_subtype_eq_ncard (F := T i ∩ A)]
    exact forest_inter_edgeSetInside_ncard_le
      (G := G) (F := T i) (U := U) hLoopless hUsub hUne (hForest i)
  have hsum :
      (∑ i : Fin n, Nat.card {e : E // e ∈ T i ∩ A}) ≤ n * (U.ncard - 1) := by
    calc
      (∑ i : Fin n, Nat.card {e : E // e ∈ T i ∩ A}) ≤
          ∑ _i : Fin n, (U.ncard - 1) := by
        exact Finset.sum_le_sum (fun i _hi => hterm i)
      _ = n * (U.ncard - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hnle : n * (U.ncard - 1) ≤ k * (U.ncard - 1) :=
    Nat.mul_le_mul_right (U.ncard - 1) hnk
  calc
    G.inducedEdgeCount U = Nat.card A := rfl
    _ ≤ Nat.card D := hA_le_D
    _ = ∑ i : Fin n, Nat.card {e : E // e ∈ T i ∩ A} := hDcard
    _ ≤ n * (U.ncard - 1) := hsum
    _ ≤ k * (U.ncard - 1) := hnle

lemma empty_isForest (G : MultiGraph V E) :
    G.IsForest (∅ : Set E) := by
  classical
  refine ⟨Set.finite_empty, by simp, by simp, ?_⟩
  intro C hC
  rcases CycleIn.edgeSupport_nonempty C with ⟨e, heC⟩
  exact hC heC

lemma exists_fin_k_forest_cover_of_canCover
    {G : MultiGraph V E} {k : ℕ}
    (hcover : G.CanCoverEdgesByAtMostKTrees k) :
    ∃ T : Fin k → Set E, (∀ i : Fin k, G.IsForest (T i)) ∧
      G.EdgeCoveredByFamily T := by
  classical
  rcases hcover with ⟨n, hnk, T, hForest, hCovered⟩
  let T' : Fin k → Set E := fun i =>
    if h : i.1 < n then T ⟨i.1, h⟩ else ∅
  refine ⟨T', ?_, ?_⟩
  · intro i
    by_cases hi : i.1 < n
    · simpa [T', hi] using hForest ⟨i.1, hi⟩
    · simpa [T', hi] using empty_isForest (G := G)
  · intro e heG
    rcases hCovered e heG with ⟨j, hej⟩
    let i : Fin k := ⟨j.1, lt_of_lt_of_le j.2 hnk⟩
    refine ⟨i, ?_⟩
    have hi : i.1 < n := j.2
    have hij : (⟨i.1, hi⟩ : Fin n) = j := Fin.ext rfl
    simpa [T', i, hi, hij] using hej

lemma cycle_shadow_degree_ge_two_of_subset_spanningTree
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) {F : Set E} (hT : G.IsSpanningTree F)
    (C : G.CycleIn) [Fintype C.support]
    [DecidableRel (((G.edgeSubgraph C.edgeSupport).induce C.support).Adj)]
    (hCF : C.edgeSupport ⊆ F)
    (v : C.support) :
    2 ≤ (((G.edgeSubgraph C.edgeSupport).induce C.support).degree v) := by
  classical
  let H : SimpleGraph C.support := (G.edgeSubgraph C.edgeSupport).induce C.support
  let ψ :
      {e : C.edgeSupport // G.Inc e.1 v.1} → H.neighborSet v := fun e =>
    let y : V := e.2.other
    let hlink : G.IsLink e.1.1 v.1 y := e.2.isLink_other
    let hyC : y ∈ C.support := (C.edges_inside e.1.2).2 y hlink.inc_right
    let yC : C.support := ⟨y, hyC⟩
    ⟨yC, by
      change H.Adj v yC
      refine ⟨?_, e.1.1, e.1.2, (C.edges_inside e.1.2).1, hlink⟩
      intro hvy
      have hval : v.1 = y := by
        simpa [yC] using hvy
      exact hLoopless ((C.edges_inside e.1.2).1) v.1 (by
        change G.IsLink e.1.1 v.1 v.1
        simpa [hval] using hlink)⟩
  have hψinj : Function.Injective ψ := by
    intro e f hef
    have hyCeq : (ψ e).1 = (ψ f).1 := congrArg Subtype.val hef
    have hy : e.2.other = f.2.other := by
      simpa [ψ] using congrArg Subtype.val hyCeq
    let vG : G.vertexSet := ⟨v.1, C.support_subset_vertexSet v.2⟩
    let eyG : G.vertexSet :=
      ⟨e.2.other, C.support_subset_vertexSet
        ((C.edges_inside e.1.2).2 e.2.other e.2.isLink_other.inc_right)⟩
    let fyG : G.vertexSet :=
      ⟨f.2.other, C.support_subset_vertexSet
        ((C.edges_inside f.1.2).2 f.2.other f.2.isLink_other.inc_right)⟩
    have hfyey : fyG = eyG := by
      exact Subtype.ext hy.symm
    have hesym :
        TreeShadow.edgeSym2 (G := G) e.1.1 (hT.2.1 (hCF e.1.2)) =
          s(vG, eyG) :=
      TreeShadow.edgeSym2_eq_of_isLink
        (G := G) (e := e.1.1) (hT.2.1 (hCF e.1.2))
        (x := vG) (y := eyG) e.2.isLink_other
    have hfsym :
        TreeShadow.edgeSym2 (G := G) f.1.1 (hT.2.1 (hCF f.1.2)) =
          s(vG, fyG) :=
      TreeShadow.edgeSym2_eq_of_isLink
        (G := G) (e := f.1.1) (hT.2.1 (hCF f.1.2))
        (x := vG) (y := fyG) f.2.isLink_other
    have hsym :
        TreeShadow.edgeSym2 (G := G) e.1.1 (hT.2.1 (hCF e.1.2)) =
          TreeShadow.edgeSym2 (G := G) f.1.1 (hT.2.1 (hCF f.1.2)) := by
      calc
        TreeShadow.edgeSym2 (G := G) e.1.1 (hT.2.1 (hCF e.1.2)) = s(vG, eyG) := hesym
        _ = s(vG, fyG) := by rw [hfyey]
        _ = TreeShadow.edgeSym2 (G := G) f.1.1 (hT.2.1 (hCF f.1.2)) := hfsym.symm
    have hef :
        e.1.1 = f.1.1 :=
      TreeShadow.edge_eq_of_edgeSym2_eq_of_isSpanningTree
        (G := G) (F := F) (a := e.1.1) (e := e.1.1) (f := f.1.1)
        hLoopless hT (hCF e.1.2) (hCF e.1.2) (hCF f.1.2) hsym
    apply Subtype.ext
    apply Subtype.ext
    exact hef
  have hsrc :
      Nat.card {e : C.edgeSupport // G.Inc e.1 v.1} = 2 :=
    C.degree_two v.1 v.2
  have hle :
      Nat.card {e : C.edgeSupport // G.Inc e.1 v.1} ≤ Nat.card (H.neighborSet v) :=
    Nat.card_le_card_of_injective ψ hψinj
  have hdegcard : Nat.card (H.neighborSet v) = H.degree v := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  rw [hsrc, hdegcard] at hle
  exact hle

lemma isSpanningTree_isForest
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hLoopless : G.Loopless) {F : Set E} (hT : G.IsSpanningTree F) :
    G.IsForest F := by
  classical
  refine ⟨hT.1, hT.2.1, ?_, ?_⟩
  · intro e heF x hloop
    exact hLoopless (hT.2.1 heF) x hloop
  · intro C hCF
    rcases CycleIn.edgeSupport_nonempty C with ⟨a, haC⟩
    let H : SimpleGraph C.support := (G.edgeSubgraph C.edgeSupport).induce C.support
    let inc : C.support ↪ G.vertexSet := {
      toFun := fun x => ⟨x.1, C.support_subset_vertexSet x.2⟩
      inj' := by
        intro x y hxy
        exact Subtype.ext (congrArg (fun z : G.vertexSet => (z : V)) hxy) }
    have hShadowTree : (TreeShadow.Shadow G F).IsTree :=
      TreeShadow.shadow_isTree_of_isSpanningTree_of_mem
        (G := G) (F := F) (e := a) hT (hCF haC)
    have hle : H ≤ (TreeShadow.Shadow G F).comap inc := by
      intro x y hxy
      rcases hxy with ⟨hne, e, heC, heG, hlink⟩
      refine ⟨?_, e, hCF heC, heG, hlink⟩
      intro h
      exact hne h
    have hHacyclic : H.IsAcyclic :=
      SimpleGraph.IsAcyclic.anti hle (hShadowTree.isAcyclic.of_comap inc)
    haveI : Fintype C.support := Fintype.ofFinite C.support
    letI : DecidableRel H.Adj := Classical.decRel _
    haveI : Nonempty C.support := C.support_nonempty.to_subtype
    have hmin : 2 ≤ H.minDegree :=
      H.le_minDegree_of_forall_le_degree 2
        (fun v => cycle_shadow_degree_ge_two_of_subset_spanningTree
          (G := G) (F := F) hLoopless hT C hCF v)
    obtain ⟨r, p, hp, _hlen⟩ :=
      (Diestel.Chapter01.proposition_1_3_1 H).2 hmin
    exact hHacyclic p hp

lemma isSpanningTreeOn_ncard_eq_sub_one
    {G : MultiGraph V E} {U : Set V} {F : Set E}
    (hF : G.IsSpanningTreeOn U F) :
    F.ncard = U.ncard - 1 := by
  rcases hF with ⟨_hUsub, _hfin, _hsub, hempty | hconn⟩
  · rcases hempty with ⟨hU, hFempty⟩
    simp [hU, hFempty]
  · omega

lemma edgeSetInside_covered_of_spanningTreesOn_bound
    {G : MultiGraph V E} [Finite V] [Finite E] {U : Set V} {k : ℕ}
    {A : Fin k → Set E}
    (hTrees : ∀ i : Fin k, G.IsSpanningTreeOn U (A i))
    (hDisj : EdgeDisjointFamily A)
    (hbound : G.inducedEdgeCount U ≤ k * (U.ncard - 1)) :
    ∀ e : E, e ∈ G.EdgeSetInside U → ∃ i : Fin k, e ∈ A i := by
  classical
  let B : Set E := ⋃ i : Fin k, A i
  have hBsub : B ⊆ G.EdgeSetInside U := by
    intro e heB
    rcases Set.mem_iUnion.mp heB with ⟨i, hei⟩
    exact (hTrees i).2.2.1 hei
  have hBcard : B.ncard = k * (U.ncard - 1) := by
    calc
      B.ncard = ∑ i : Fin k, (A i).ncard := by
        change (⋃ i : Fin k, A i).ncard = ∑ i : Fin k, (A i).ncard
        rw [Set.ncard_iUnion_of_finite]
        · exact finsum_eq_finset_sum_of_support_subset _ (by intro i _hi; simp)
        · intro i
          exact (hTrees i).2.1
        · exact hDisj
      _ = ∑ _i : Fin k, (U.ncard - 1) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact isSpanningTreeOn_ncard_eq_sub_one (G := G) (U := U) (F := A i)
          (hTrees i)
      _ = k * (U.ncard - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hInsideCard :
      (G.EdgeSetInside U).ncard ≤ k * (U.ncard - 1) := by
    simpa [inducedEdgeCount, TreeShadow.natCard_subtype_eq_ncard
      (F := G.EdgeSetInside U)] using hbound
  have hInside_eq_B : B = G.EdgeSetInside U := by
    exact Set.eq_of_subset_of_ncard_le hBsub (by simpa [hBcard] using hInsideCard)
  intro e heInside
  have heB : e ∈ B := by
    simpa [hInside_eq_B] using heInside
  exact Set.mem_iUnion.mp heB

lemma connected_canCoverEdgesByAtMostKTrees_of_induced_bound
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    (hk : 0 < k) (hLoopless : G.Loopless) (hConn : G.Connected)
    (hbound : ∀ U : Set V, U ⊆ G.vertexSet → U.Nonempty →
      G.inducedEdgeCount U ≤ k * (U.ncard - 1)) :
    G.CanCoverEdgesByAtMostKTrees k := by
  classical
  rcases theorem_2_4_4 (G := G) k hLoopless hConn with ⟨P, hPack⟩
  rcases hPack with ⟨hP, hInside, hQuot⟩
  rcases hQuot with ⟨Q, hQtrees, hQcover⟩
  have hVne : G.vertexSet.Nonempty := by
    rcases hConn.nonempty with ⟨v⟩
    exact ⟨v.1, v.2⟩
  have hPne : P.Nonempty := by
    rcases hVne with ⟨v, hv⟩
    rcases hP.2.2 v hv with ⟨U, hU, _hvU⟩
    exact ⟨U, hU⟩
  let A : {U : Set V // U ∈ P} → Fin k → Set E :=
    fun U => Classical.choose (hInside U.1 U.2)
  have hA_tree :
      ∀ U : {U : Set V // U ∈ P}, ∀ i : Fin k,
        G.IsSpanningTreeOn U.1 (A U i) := by
    intro U
    exact (Classical.choose_spec (hInside U.1 U.2)).1
  have hA_disj :
      ∀ U : {U : Set V // U ∈ P}, EdgeDisjointFamily (A U) := by
    intro U
    exact (Classical.choose_spec (hInside U.1 U.2)).2
  refine ⟨k, le_rfl, fun i : Fin k => G.gluedTreeEdgeSet (fun U => A U i) (Q i), ?_, ?_⟩
  · intro i
    exact isSpanningTree_isForest
      (G := G) hLoopless
      (gluedTreeEdgeSet_isSpanningTree
        (G := G) (P := P) (A := fun U => A U i) (Q := Q i)
        hP hPne (fun U => hA_tree U i) (hQtrees i))
  · intro e heG
    by_cases hCross : G.IsCrossEdge P e
    · let q : G.CrossEdge P := ⟨e, hCross⟩
      rcases hQcover q with ⟨i, hqi⟩
      refine ⟨i, ?_⟩
      exact mem_gluedTreeEdgeSet_quotient
        (G := G) (A := fun U => A U i) (Q := Q i) hqi
    · rcases G.exists_isLink_of_mem_edgeSet heG with ⟨x, y, hlink⟩
      rcases hP.2.2 x hlink.left_mem with ⟨U, hU, hxU⟩
      rcases hP.2.2 y hlink.right_mem with ⟨W, hW, hyW⟩
      have hUW : U = W := by
        by_contra hne
        exact hCross ⟨heG, x, y, hlink, U, hU, W, hW, hne, hxU, hyW⟩
      subst W
      let U' : {U : Set V // U ∈ P} := ⟨U, hU⟩
      have heInside : e ∈ G.EdgeSetInside U := by
        refine ⟨heG, ?_⟩
        intro z hz
        rcases hz.eq_or_eq_of_isLink hlink with rfl | rfl
        · exact hxU
        · exact hyW
      have hcoverInside :
          ∃ i : Fin k, e ∈ A U' i :=
        edgeSetInside_covered_of_spanningTreesOn_bound
          (G := G) (U := U) (k := k) (A := A U')
          (hA_tree U') (hA_disj U')
          (hbound U (hP.1 U hU).2 (hP.1 U hU).1) e heInside
      rcases hcoverInside with ⟨i, hei⟩
      exact ⟨i, mem_gluedTreeEdgeSet_internal
        (G := G) (A := fun U => A U i) (Q := Q i) U' hei⟩

lemma canCoverEdgesByAtMostKTrees_of_induced_bound
    {G : MultiGraph V E} [Finite V] [Finite E] {k : ℕ}
    (hk : 0 < k) (hLoopless : G.Loopless)
    (hbound : ∀ U : Set V, U ⊆ G.vertexSet → U.Nonempty →
      G.inducedEdgeCount U ≤ k * (U.ncard - 1)) :
    G.CanCoverEdgesByAtMostKTrees k := by
  classical
  let Comp := G.toSimpleGraph.ConnectedComponent
  let U : Comp → Set V := fun C => componentVertexSet G C
  have hCompCover :
      ∀ C : Comp, ∃ T : Fin k → Set E,
        (∀ i : Fin k, IsForest (G.induce (U C)) (T i)) ∧
          EdgeCoveredByFamily (G.induce (U C)) T := by
    intro C
    have hCov :
        CanCoverEdgesByAtMostKTrees (G.induce (U C)) k :=
      connected_canCoverEdgesByAtMostKTrees_of_induced_bound
        (G := G.induce (U C)) (k := k) hk
        (induce_loopless (G := G) hLoopless (U C))
        (induced_component_connected G C)
        (by
          intro W hWsub hWne
          have hWsubG : W ⊆ G.vertexSet := by
            intro x hx
            have hxU : x ∈ U C := by
              exact hWsub hx
            exact componentVertexSet_subset G C hxU
          exact (inducedEdgeCount_induce_le (G := G) (U C) W).trans
            (hbound W hWsubG hWne))
    exact exists_fin_k_forest_cover_of_canCover hCov
  choose T hT using hCompCover
  let Tglobal : Fin k → Set E := fun i => ⋃ C : Comp, T C i
  refine ⟨k, le_rfl, Tglobal, ?_, ?_⟩
  · intro i
    refine ⟨Set.toFinite _, ?_, ?_, ?_⟩
    · intro e he
      rcases Set.mem_iUnion.mp he with ⟨C, heC⟩
      have heInd : e ∈ (G.induce (U C)).edgeSet := ((hT C).1 i).2.1 heC
      rcases heInd with ⟨x, y, hlink, _hxU, _hyU⟩
      exact hlink.edge_mem
    · intro e he x hloop
      exact hLoopless (((show Tglobal i ⊆ G.edgeSet from by
        intro f hf
        rcases Set.mem_iUnion.mp hf with ⟨C, hfC⟩
        have hfInd : f ∈ (G.induce (U C)).edgeSet := ((hT C).1 i).2.1 hfC
        rcases hfInd with ⟨a, b, hlink, _ha, _hb⟩
        exact hlink.edge_mem) he)) x hloop
    · intro D hDsub
      rcases D.support_nonempty with ⟨r, hr⟩
      let C₀ : Comp :=
        G.toSimpleGraph.connectedComponentMk
          (⟨r, D.support_subset_vertexSet hr⟩ : G.vertexSet)
      have edge_mem_component_tree :
          ∀ ⦃e : E⦄, e ∈ D.edgeSupport → e ∈ T C₀ i := by
        intro e heD
        have heGlobal : e ∈ Tglobal i := hDsub heD
        rcases Set.mem_iUnion.mp heGlobal with ⟨C, heC⟩
        have heIndC : e ∈ (G.induce (U C)).edgeSet := ((hT C).1 i).2.1 heC
        rcases heIndC with ⟨x, y, hlink, hxUC, _hyUC⟩
        have hxD : x ∈ D.support := (D.edges_inside heD).2 x hlink.inc_left
        rcases hxUC with ⟨hxG, hxC⟩
        have hxCompC :
            G.toSimpleGraph.connectedComponentMk (⟨x, hxG⟩ : G.vertexSet) = C :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff C _).1 hxC
        have hxCompC₀ :
            G.toSimpleGraph.connectedComponentMk (⟨x, hxG⟩ : G.vertexSet) = C₀ := by
          have hxEq :
              (⟨x, D.support_subset_vertexSet hxD⟩ : G.vertexSet) =
                (⟨x, hxG⟩ : G.vertexSet) := Subtype.ext rfl
          have hraw := cycle_support_component_eq (G := G) D hr hxD
          rw [hxEq] at hraw
          exact hraw
        have hCeq : C = C₀ := hxCompC.symm.trans hxCompC₀
        simpa [hCeq] using heC
      have hDsubInd :
          D.edgeSupport ⊆ (G.induce (U C₀)).edgeSet := by
        intro e heD
        have heC₀ : e ∈ T C₀ i := edge_mem_component_tree heD
        exact ((hT C₀).1 i).2.1 heC₀
      exact ((hT C₀).1 i).2.2.2
        (cycleIn_of_induce (G := G) (U := U C₀) D hDsubInd)
        (by intro e heD; exact edge_mem_component_tree heD)
  · intro e heG
    rcases G.exists_isLink_of_mem_edgeSet heG with ⟨x, y, hlink⟩
    let xG : G.vertexSet := ⟨x, hlink.left_mem⟩
    let yG : G.vertexSet := ⟨y, hlink.right_mem⟩
    let C : Comp := G.toSimpleGraph.connectedComponentMk xG
    have hxy : xG ≠ yG := by
      intro h
      have hval : x = y := congrArg (fun z : G.vertexSet => (z : V)) h
      exact hLoopless heG x (by
        change G.IsLink e x x
        simpa [hval] using hlink)
    have hAdj : G.toSimpleGraph.Adj xG yG := ⟨hxy, e, hlink⟩
    have hyC : yG ∈ C.supp := by
      have hcomp : G.toSimpleGraph.connectedComponentMk yG = C := by
        simpa [C] using SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hAdj.symm
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff C yG).2 hcomp
    have heInd : e ∈ (G.induce (U C)).edgeSet := by
      refine ⟨x, y, hlink, ?_, ?_⟩
      · exact ⟨xG.2, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
      · exact ⟨yG.2, hyC⟩
    rcases (hT C).2 e heInd with ⟨i, hei⟩
    exact ⟨i, Set.mem_iUnion.mpr ⟨C, hei⟩⟩

end TreeCovering

end MultiGraph

end Chapter02
end Diestel
