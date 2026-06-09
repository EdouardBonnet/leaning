import Chapter02.spanning_tree_exchange_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

namespace TreeShadow

lemma inducedShadow_edge_exists_label {G : MultiGraph V E} {F : Set E} {U : Set V}
    (q : ((G.edgeSubgraph F).induce U).edgeSet) :
    ∃ e : E, e ∈ F ∧ e ∈ G.edgeSet ∧
      ∃ x y : U, (q : Sym2 U) = s(x, y) ∧ G.IsLink e x.1 y.1 := by
  classical
  rcases q with ⟨qval, hq⟩
  change ∃ e : E, e ∈ F ∧ e ∈ G.edgeSet ∧
      ∃ x y : U, qval = s(x, y) ∧ G.IsLink e x.1 y.1
  induction qval using Sym2.inductionOn with
  | hf x y =>
      have hxy : ((G.edgeSubgraph F).induce U).Adj x y := by
        simpa [SimpleGraph.mem_edgeSet] using hq
      rcases hxy with ⟨_hne, e, heF, heG, hlink⟩
      exact ⟨e, heF, heG, x, y, rfl, hlink⟩

noncomputable def inducedShadowEdgeLabel {G : MultiGraph V E} {F : Set E} {U : Set V}
    (q : ((G.edgeSubgraph F).induce U).edgeSet) : E :=
  Classical.choose (inducedShadow_edge_exists_label (G := G) (F := F) (U := U) q)

lemma inducedShadowEdgeLabel_mem {G : MultiGraph V E} {F : Set E} {U : Set V}
    (q : ((G.edgeSubgraph F).induce U).edgeSet) :
    inducedShadowEdgeLabel (G := G) (F := F) (U := U) q ∈ F :=
  (Classical.choose_spec
    (inducedShadow_edge_exists_label (G := G) (F := F) (U := U) q)).1

lemma inducedShadowEdgeLabel_injective {G : MultiGraph V E} {F : Set E} {U : Set V} :
    Function.Injective (fun q : ((G.edgeSubgraph F).induce U).edgeSet =>
      (⟨inducedShadowEdgeLabel (G := G) (F := F) (U := U) q,
        inducedShadowEdgeLabel_mem (G := G) (F := F) (U := U) q⟩ : F)) := by
  classical
  intro q r hqr
  apply Subtype.ext
  obtain ⟨x, y, hqval, hqLink⟩ :=
    (Classical.choose_spec
      (inducedShadow_edge_exists_label (G := G) (F := F) (U := U) q)).2.2
  obtain ⟨x', y', hrval, hrLink⟩ :=
    (Classical.choose_spec
      (inducedShadow_edge_exists_label (G := G) (F := F) (U := U) r)).2.2
  change G.IsLink (inducedShadowEdgeLabel (G := G) (F := F) (U := U) q) x.1 y.1
    at hqLink
  change G.IsLink (inducedShadowEdgeLabel (G := G) (F := F) (U := U) r) x'.1 y'.1
    at hrLink
  have hsame :
      inducedShadowEdgeLabel (G := G) (F := F) (U := U) q =
        inducedShadowEdgeLabel (G := G) (F := F) (U := U) r := by
    exact congrArg Subtype.val hqr
  have hrLink' :
      G.IsLink (inducedShadowEdgeLabel (G := G) (F := F) (U := U) q) x'.1 y'.1 := by
    simpa [hsame] using hrLink
  rw [hqval, hrval]
  rcases hqLink.eq_and_eq_or_eq_and_eq hrLink' with h | h
  · rcases h with ⟨hxx, hyy⟩
    have hx : x = x' := Subtype.ext hxx
    have hy : y = y' := Subtype.ext hyy
    subst x'
    subst y'
    rfl
  · rcases h with ⟨hxy, hyx⟩
    have hx : x = y' := Subtype.ext hxy
    have hy : y = x' := Subtype.ext hyx
    subst y'
    subst x'
    exact Sym2.eq_swap

lemma inducedShadow_edgeSet_natCard_le {G : MultiGraph V E} [Finite E]
    {F : Set E} {U : Set V} :
    Nat.card ((G.edgeSubgraph F).induce U).edgeSet ≤ Nat.card F :=
  Nat.card_le_card_of_injective
    (fun q : ((G.edgeSubgraph F).induce U).edgeSet =>
      (⟨inducedShadowEdgeLabel (G := G) (F := F) (U := U) q,
        inducedShadowEdgeLabel_mem (G := G) (F := F) (U := U) q⟩ : F))
    (inducedShadowEdgeLabel_injective (G := G) (F := F) (U := U))

noncomputable def edgeSym2InInduced {G : MultiGraph V E} {U : Set V}
    (A : Set E) (hLoopless : G.Loopless) (hA : A ⊆ G.EdgeSetInside U) :
    A → ((G.edgeSubgraph A).induce U).edgeSet :=
  fun e =>
    let heG : e.1 ∈ G.edgeSet := (hA e.2).1
    let x : V := edgeLeft (G := G) e.1 heG
    let y : V := edgeRight (G := G) e.1 heG
    let hlink : G.IsLink e.1 x y := edgeLeft_isLink_edgeRight (G := G) e.1 heG
    let hxU : x ∈ U := (hA e.2).2 x hlink.inc_left
    let hyU : y ∈ U := (hA e.2).2 y hlink.inc_right
    ⟨s(⟨x, hxU⟩, ⟨y, hyU⟩), by
      rw [SimpleGraph.mem_edgeSet]
      change ((G.edgeSubgraph A).induce U).Adj (⟨x, hxU⟩ : U) (⟨y, hyU⟩ : U)
      refine ⟨?_, e.1, e.2, heG, hlink⟩
      intro hxy
      have hval : x = y := by simpa using hxy
      exact hLoopless heG x (by
        change G.IsLink e.1 x x
        simpa [hval] using hlink)⟩

lemma edgeSym2InInduced_injective_of_subset_spanningTree
    {G : MultiGraph V E} [Finite V] [Finite E]
    {F A : Set E} {U : Set V}
    (hLoopless : G.Loopless) (hF : G.IsSpanningTree F)
    (hUsub : U ⊆ G.vertexSet) (hAF : A ⊆ F) (hA : A ⊆ G.EdgeSetInside U) :
    Function.Injective (edgeSym2InInduced (G := G) (A := A) hLoopless hA) := by
  classical
  intro e f hef
  let inc : U ↪ G.vertexSet := {
    toFun := fun x => ⟨x.1, hUsub x.2⟩
    inj' := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : G.vertexSet => z.1) hxy) }
  have hsymU :
      ((edgeSym2InInduced (G := G) (A := A) hLoopless hA e : ((G.edgeSubgraph A).induce U).edgeSet) :
        Sym2 U) =
      ((edgeSym2InInduced (G := G) (A := A) hLoopless hA f : ((G.edgeSubgraph A).induce U).edgeSet) :
        Sym2 U) :=
    congrArg Subtype.val hef
  have hsymG :
      edgeSym2 (G := G) e.1 (hF.2.1 (hAF e.2)) =
        edgeSym2 (G := G) f.1 (hF.2.1 (hAF f.2)) := by
    simpa [edgeSym2InInduced, edgeSym2, inc] using
      congrArg (Function.Embedding.sym2Map inc) hsymU
  apply Subtype.ext
  exact edge_eq_of_edgeSym2_eq_of_isSpanningTree
    (G := G) (F := F) (a := e.1) (e := e.1) (f := f.1)
    hLoopless hF (hAF e.2) (hAF e.2) (hAF f.2) hsymG

lemma inducedShadow_edgeSet_natCard_eq_of_subset_spanningTree
    {G : MultiGraph V E} [Finite V] [Finite E]
    {F A : Set E} {U : Set V}
    (hLoopless : G.Loopless) (hF : G.IsSpanningTree F)
    (hUsub : U ⊆ G.vertexSet) (hAF : A ⊆ F) (hA : A ⊆ G.EdgeSetInside U) :
    Nat.card ((G.edgeSubgraph A).induce U).edgeSet = A.ncard := by
  classical
  have hle_label :
      Nat.card ((G.edgeSubgraph A).induce U).edgeSet ≤ Nat.card A :=
    inducedShadow_edgeSet_natCard_le (G := G) (F := A) (U := U)
  have hle_edge :
      Nat.card A ≤ Nat.card ((G.edgeSubgraph A).induce U).edgeSet :=
    Nat.card_le_card_of_injective
      (edgeSym2InInduced (G := G) (A := A) hLoopless hA)
      (edgeSym2InInduced_injective_of_subset_spanningTree
        (G := G) (F := F) (A := A) (U := U) hLoopless hF hUsub hAF hA)
  have hcard : Nat.card ((G.edgeSubgraph A).induce U).edgeSet = Nat.card A :=
    le_antisymm hle_label hle_edge
  simpa [natCard_subtype_eq_ncard (F := A)] using hcard

lemma isSpanningTreeOn_of_connected_subset_spanningTree
    {G : MultiGraph V E} [Finite V] [Finite E]
    {F A : Set E} {U : Set V}
    (hLoopless : G.Loopless) (hF : G.IsSpanningTree F)
    (hUsub : U ⊆ G.vertexSet) (hAF : A ⊆ F) (hA : A ⊆ G.EdgeSetInside U)
    (hconn : ((G.edgeSubgraph A).induce U).Connected) :
    G.IsSpanningTreeOn U A := by
  classical
  let inc : U ↪ G.vertexSet := {
    toFun := fun x => ⟨x.1, hUsub x.2⟩
    inj' := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : G.vertexSet => z.1) hxy) }
  have hShadowTree : (Shadow G F).IsTree := by
    have hvG : G.vertexSet.Nonempty := by
      rcases hconn.nonempty with ⟨x⟩
      exact ⟨x.1, hUsub x.2⟩
    by_cases hFempty : F = ∅
    · rw [SimpleGraph.isTree_iff_connected_and_card]
      obtain ⟨hconnF, hcardF⟩ :=
        isSpanningTree_connected_card_of_vertex_nonempty
          (G := G) (F := F) hF hvG
      refine ⟨hconnF, ?_⟩
      have hedgeEmpty : (Shadow G F).edgeSet = ∅ := by
        ext q
        constructor
        · intro hq
          rcases shadow_edge_exists_label (G := G) (F := F) ⟨q, hq⟩ with
            ⟨e, heF, _heG, _x, _y, _hq, _hlink⟩
          exact False.elim (by simpa [hFempty] using heF)
        · intro hq
          exact False.elim (by simpa using hq)
      have hEdgeCard : Nat.card (Shadow G F).edgeSet = 0 := by
        simp [hedgeEmpty]
      have hFcard : F.ncard = 0 := by
        simp [hFempty]
      calc
        Nat.card (Shadow G F).edgeSet + 1 = F.ncard + 1 := by
          rw [hEdgeCard, hFcard]
        _ = G.vertexSet.ncard := hcardF
        _ = Nat.card G.vertexSet := by simp
    · rcases Set.nonempty_iff_ne_empty.mpr hFempty with ⟨e, heF⟩
      exact shadow_isTree_of_isSpanningTree_of_mem
        (G := G) (F := F) (e := e) hF heF
  have hle :
      (G.edgeSubgraph A).induce U ≤ (Shadow G F).comap inc := by
    intro x y hxy
    rcases hxy with ⟨hne, e, heA, heG, hlink⟩
    exact ⟨hne, e, hAF heA, heG, hlink⟩
  have hac :
      ((G.edgeSubgraph A).induce U).IsAcyclic :=
    SimpleGraph.IsAcyclic.anti hle (hShadowTree.isAcyclic.of_comap inc)
  have hTree : ((G.edgeSubgraph A).induce U).IsTree :=
    ⟨hconn, hac⟩
  have hEdgeCard :
      Nat.card ((G.edgeSubgraph A).induce U).edgeSet = A.ncard :=
    inducedShadow_edgeSet_natCard_eq_of_subset_spanningTree
      (G := G) (F := F) (A := A) (U := U) hLoopless hF hUsub hAF hA
  refine ⟨hUsub, Set.toFinite A, hA, Or.inr ⟨hconn, ?_⟩⟩
  have hcard :=
    (SimpleGraph.isTree_iff_connected_and_card
      (G := (G.edgeSubgraph A).induce U)).1 hTree |>.2
  calc
    A.ncard + 1 = Nat.card ((G.edgeSubgraph A).induce U).edgeSet + 1 := by
      rw [hEdgeCard]
    _ = Nat.card U := hcard
    _ = U.ncard := by simp

end TreeShadow

end MultiGraph

end Chapter02
end Diestel
