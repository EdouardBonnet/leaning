import «statements-and-proofs».Exponent7.CutResponder.GenericFrontierAudit
import «statements-and-proofs».CutMatchingGameDefs

/-!
# Prescribed bisection routing and side-changing traces

This is the first application-specific replacement for the generic prescribed
matching frontier.  The two sides of the cut are supplied explicitly.  A
node-well-linked anchor set gives a perfect routing from the left anchors to
the right anchors, but does not prescribe its endpoint pairing.

For every routed path we retain:

* its original left and right row labels;
* the ordered list of vertices at which it meets an active selected row;
* the unique active row containing each such contact.

The path is then trimmed from its last left-side contact before its first
right-side contact.  Mathlib's two-stage `cleanBetweenTerminalSets`
construction implements exactly this operation.  The resulting transition
has no internal active-row contact, so its endpoints are consecutive in the
ordered selected-row trace.  Since each transition is a subpath of a member
of the original perfect packing, all transitions remain pairwise
node-disjoint.

This module is independent of the frozen conditional exponent-seven endpoint
and adds no axiom.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T : Finset V}

theorem selectedRowVertexSet_union
    (R : PathPacking G S T) (U W : Finset R.Index) :
    selectedRowVertexSet R (U ∪ W) =
      selectedRowVertexSet R U ∪ selectedRowVertexSet R W := by
  classical
  ext v
  simp only [mem_selectedRowVertexSet, Finset.mem_union]
  constructor
  · rintro ⟨r, hrU | hrW, hvr⟩
    · exact Or.inl ⟨r, hrU, hvr⟩
    · exact Or.inr ⟨r, hrW, hvr⟩
  · rintro (⟨r, hrU, hvr⟩ | ⟨r, hrW, hvr⟩)
    · exact ⟨r, Or.inl hrU, hvr⟩
    · exact ⟨r, Or.inr hrW, hvr⟩

/-- A routing between two explicitly supplied, disjoint, equally large
families of row anchors.  Unlike `BalancedAnchorRouting`, this object does not
choose the two sides. -/
structure PrescribedBisectionRouting
    (R : PathPacking G S T) (anchor : R.Index → V)
    (U W : Finset R.Index) (C : Finset V) where
  anchor_mem : ∀ r, anchor r ∈ (R.path r).vertexSet
  sides_disjoint : Disjoint U W
  side_card_eq : U.card = W.card
  routes : PerfectPathPacking G (U.image anchor) (W.image anchor)
  routes_card : routes.card = U.card
  routes_stay : routes.toPathPacking.StaysIn C

/-- Node-well-linked anchors route any two explicitly supplied disjoint
equal-size index sets. -/
noncomputable def prescribedBisectionRouting
    (R : PathPacking G S T) (anchor : R.Index → V)
    (hanchor : ∀ r, anchor r ∈ (R.path r).vertexSet)
    (U W : Finset R.Index) (C : Finset V)
    (hdisjoint : Disjoint U W) (hcard : U.card = W.card)
    (hwell :
      NodeWellLinkedIn G C
        ((Finset.univ : Finset R.Index).image anchor)) :
    PrescribedBisectionRouting R anchor U W C := by
  classical
  have hinj : Function.Injective anchor :=
    rowAnchor_injective R anchor hanchor
  have hUsub :
      U.image anchor ⊆
        (Finset.univ : Finset R.Index).image anchor := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  have hWsub :
      W.image anchor ⊆
        (Finset.univ : Finset R.Index).image anchor := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  have hImageDisjoint : Disjoint (U.image anchor) (W.image anchor) := by
    rw [Finset.disjoint_left]
    intro v hvU hvW
    rcases Finset.mem_image.mp hvU with ⟨r, hrU, hrv⟩
    rcases Finset.mem_image.mp hvW with ⟨s, hsW, hsv⟩
    have hrs : r = s := hinj (hrv.trans hsv.symm)
    exact Finset.disjoint_left.mp hdisjoint hrU (by simpa [hrs] using hsW)
  let routed := Classical.choose (hwell.2 hUsub hWsub hImageDisjoint)
  have hrouted :=
    Classical.choose_spec (hwell.2 hUsub hWsub hImageDisjoint)
  let P := routed
  have hPcard :
      P.card = min (U.image anchor).card (W.image anchor).card := by
    simpa [P, routed] using hrouted.1
  have hPstay : P.StaysIn C := by
    simpa [P, routed] using hrouted.2
  have hUimageCard : (U.image anchor).card = U.card := by
    rw [Finset.card_image_of_injective]
    exact hinj
  have hWimageCard : (W.image anchor).card = W.card := by
    rw [Finset.card_image_of_injective]
    exact hinj
  have hPcardU : P.card = (U.image anchor).card := by
    simpa [hUimageCard, hWimageCard, hcard] using hPcard
  have hPcardW : P.card = (W.image anchor).card := by
    simpa [hUimageCard, hWimageCard, hcard] using hPcard
  let Pperfect := P.toPerfectOfCardEq hPcardU hPcardW
  exact
    { anchor_mem := hanchor
      sides_disjoint := hdisjoint
      side_card_eq := hcard
      routes := Pperfect
      routes_card := by
        simpa [Pperfect, PerfectPathPacking.card,
          PathPacking.toPerfectOfCardEq, PathPacking.card,
          hUimageCard] using hPcardU
      routes_stay := by
        simpa [Pperfect, PathPacking.toPerfectOfCardEq] using
          PathPacking.orient_staysIn hPstay }

namespace PrescribedBisectionRouting

variable
    {R : PathPacking G S T} {anchor : R.Index → V}
    {U W : Finset R.Index} {C : Finset V}

/-- The original left row label of a routed path. -/
noncomputable def sourceLabel
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : {r : R.Index // r ∈ U} :=
  let h :=
    Finset.mem_image.mp (B.routes.source_mem p)
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

@[simp] theorem source_eq_anchor_sourceLabel
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).source = anchor (B.sourceLabel p).1 := by
  classical
  exact
    (Classical.choose_spec
      (Finset.mem_image.mp (B.routes.source_mem p))).2.symm

/-- The original right row label of a routed path. -/
noncomputable def targetLabel
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : {r : R.Index // r ∈ W} :=
  let h :=
    Finset.mem_image.mp (B.routes.target_mem p)
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

@[simp] theorem target_eq_anchor_targetLabel
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).target = anchor (B.targetLabel p).1 := by
  classical
  exact
    (Classical.choose_spec
      (Finset.mem_image.mp (B.routes.target_mem p))).2.symm

theorem sourceLabel_injective
    (B : PrescribedBisectionRouting R anchor U W C) :
    Function.Injective B.sourceLabel := by
  intro p q hpq
  apply B.routes.source_bijective.1
  apply Subtype.ext
  change (B.routes.path p).source = (B.routes.path q).source
  rw [B.source_eq_anchor_sourceLabel, B.source_eq_anchor_sourceLabel, hpq]

theorem targetLabel_injective
    (B : PrescribedBisectionRouting R anchor U W C) :
    Function.Injective B.targetLabel := by
  intro p q hpq
  apply B.routes.target_bijective.1
  apply Subtype.ext
  change (B.routes.path p).target = (B.routes.path q).target
  rw [B.target_eq_anchor_targetLabel, B.target_eq_anchor_targetLabel, hpq]

/-- The active selected rows are exactly the two supplied sides. -/
noncomputable def activeRows
    (_B : PrescribedBisectionRouting R anchor U W C) :
    Finset R.Index :=
  U ∪ W

/-- Ordered selected-row contacts of a routed path.  These are actual route
vertices, not merely an unordered set of row labels. -/
noncomputable def selectedRowIntersectionTrace
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : List V := by
  classical
  exact (B.routes.path p).walk.support.filter
    (fun v => v ∈ selectedRowVertexSet R B.activeRows)

theorem mem_selectedRowIntersectionTrace
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) (v : V) :
    v ∈ B.selectedRowIntersectionTrace p ↔
      v ∈ (B.routes.path p).vertexSet ∧
        v ∈ selectedRowVertexSet R B.activeRows := by
  classical
  simp [selectedRowIntersectionTrace, GraphPath.vertexSet]

theorem selectedRowIntersectionTrace_nodup
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.selectedRowIntersectionTrace p).Nodup := by
  classical
  exact (B.routes.path p).isPath.support_nodup.filter _

theorem route_source_mem_activeRows
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).source ∈
      selectedRowVertexSet R B.activeRows := by
  apply (mem_selectedRowVertexSet R B.activeRows).2
  refine ⟨(B.sourceLabel p).1, ?_, ?_⟩
  · exact Finset.mem_union_left W (B.sourceLabel p).2
  · simpa [B.source_eq_anchor_sourceLabel p] using
      B.anchor_mem (B.sourceLabel p).1

theorem route_target_mem_activeRows
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).target ∈
      selectedRowVertexSet R B.activeRows := by
  apply (mem_selectedRowVertexSet R B.activeRows).2
  refine ⟨(B.targetLabel p).1, ?_, ?_⟩
  · exact Finset.mem_union_right U (B.targetLabel p).2
  · simpa [B.target_eq_anchor_targetLabel p] using
      B.anchor_mem (B.targetLabel p).1

theorem route_source_mem_trace
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).source ∈
      B.selectedRowIntersectionTrace p := by
  exact (B.mem_selectedRowIntersectionTrace p _).2
    ⟨GraphPath.source_mem_vertexSet _, B.route_source_mem_activeRows p⟩

theorem route_target_mem_trace
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).target ∈
      B.selectedRowIntersectionTrace p := by
  exact (B.mem_selectedRowIntersectionTrace p _).2
    ⟨GraphPath.target_mem_vertexSet _, B.route_target_mem_activeRows p⟩

/-- The unique active row containing a selected-row contact. -/
noncomputable def traceRow
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index)
    (v : V) (hv : v ∈ B.selectedRowIntersectionTrace p) :
    {r : R.Index // r ∈ B.activeRows} := by
  classical
  have hvRows :=
    (B.mem_selectedRowIntersectionTrace p v).1 hv
  exact ⟨Classical.choose
      ((mem_selectedRowVertexSet R B.activeRows).1 hvRows.2),
    (Classical.choose_spec
      ((mem_selectedRowVertexSet R B.activeRows).1 hvRows.2)).1⟩

theorem traceRow_vertex_mem
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index)
    (v : V) (hv : v ∈ B.selectedRowIntersectionTrace p) :
    v ∈ (R.path (B.traceRow p v hv).1).vertexSet := by
  classical
  unfold traceRow
  exact
    (Classical.choose_spec
      ((mem_selectedRowVertexSet R B.activeRows).1
        ((B.mem_selectedRowIntersectionTrace p v).1 hv).2)).2

theorem traceRow_unique
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index)
    (v : V) (hv : v ∈ B.selectedRowIntersectionTrace p)
    {r : R.Index} (hr : r ∈ B.activeRows)
    (hvr : v ∈ (R.path r).vertexSet) :
    r = (B.traceRow p v hv).1 := by
  by_contra hne
  exact Finset.disjoint_left.mp (R.node_disjoint hne)
    hvr (B.traceRow_vertex_mem p v hv)

/-- A single record retaining both original endpoint labels and the ordered
selected-row trace. -/
structure LabelledRoute
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) where
  source : {r : R.Index // r ∈ U}
  target : {r : R.Index // r ∈ W}
  trace : List V
  source_eq : (B.routes.path p).source = anchor source.1
  target_eq : (B.routes.path p).target = anchor target.1
  trace_eq : trace = B.selectedRowIntersectionTrace p
  trace_nodup : trace.Nodup
  source_mem_trace : (B.routes.path p).source ∈ trace
  target_mem_trace : (B.routes.path p).target ∈ trace

noncomputable def labelledRoute
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    B.LabelledRoute p where
  source := B.sourceLabel p
  target := B.targetLabel p
  trace := B.selectedRowIntersectionTrace p
  source_eq := B.source_eq_anchor_sourceLabel p
  target_eq := B.target_eq_anchor_targetLabel p
  trace_eq := rfl
  trace_nodup := B.selectedRowIntersectionTrace_nodup p
  source_mem_trace := B.route_source_mem_trace p
  target_mem_trace := B.route_target_mem_trace p

theorem route_connects_side_row_unions
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routes.path p).Connects
      (selectedRowVertexSet R U)
      (selectedRowVertexSet R W) := by
  apply Or.inl
  constructor
  · apply (mem_selectedRowVertexSet R U).2
    exact
      ⟨(B.sourceLabel p).1, (B.sourceLabel p).2,
        by
          simpa [B.source_eq_anchor_sourceLabel p] using
            B.anchor_mem (B.sourceLabel p).1⟩
  · apply (mem_selectedRowVertexSet R W).2
    exact
      ⟨(B.targetLabel p).1, (B.targetLabel p).2,
        by
          simpa [B.target_eq_anchor_targetLabel p] using
            B.anchor_mem (B.targetLabel p).1⟩

/-- The consecutive side-changing transition selected on one routed path. -/
noncomputable def sideChangingPath
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : GraphPath G :=
  (B.routes.path p).cleanBetweenTerminalSets
    (B.route_connects_side_row_unions p)

theorem sideChangingPath_vertexSet_subset_route
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).vertexSet ⊆
      (B.routes.path p).vertexSet := by
  exact
    (B.routes.path p).cleanBetweenTerminalSets_vertexSet_subset
      (B.route_connects_side_row_unions p)

theorem sideChangingPath_source_mem_leftRows
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).source ∈ selectedRowVertexSet R U := by
  exact
    (B.routes.path p).cleanBetweenTerminalSets_source_mem
      (B.route_connects_side_row_unions p)

theorem sideChangingPath_target_mem_rightRows
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).target ∈ selectedRowVertexSet R W := by
  exact
    (B.routes.path p).cleanBetweenTerminalSets_target_mem
      (B.route_connects_side_row_unions p)

/-- The left row hit by the selected side-changing transition. -/
noncomputable def transitionLeftRow
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : {r : R.Index // r ∈ U} := by
  classical
  have h :=
    (mem_selectedRowVertexSet R U).1
      (B.sideChangingPath_source_mem_leftRows p)
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem sideChangingPath_source_mem_transitionLeftRow
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).source ∈
      (R.path (B.transitionLeftRow p).1).vertexSet := by
  classical
  unfold transitionLeftRow
  exact
    (Classical.choose_spec
      ((mem_selectedRowVertexSet R U).1
        (B.sideChangingPath_source_mem_leftRows p))).2

/-- The right row hit by the selected side-changing transition. -/
noncomputable def transitionRightRow
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : {r : R.Index // r ∈ W} := by
  classical
  have h :=
    (mem_selectedRowVertexSet R W).1
      (B.sideChangingPath_target_mem_rightRows p)
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem sideChangingPath_target_mem_transitionRightRow
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).target ∈
      (R.path (B.transitionRightRow p).1).vertexSet := by
  classical
  unfold transitionRightRow
  exact
    (Classical.choose_spec
      ((mem_selectedRowVertexSet R W).1
        (B.sideChangingPath_target_mem_rightRows p))).2

/-- Endpoint cleanliness is the formal statement that the two selected-row
contacts are consecutive in the ordered selected-row trace. -/
theorem sideChangingPath_consecutive_active_contacts
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).InternallyDisjointFromSet
      (selectedRowVertexSet R B.activeRows) := by
  rw [activeRows, selectedRowVertexSet_union]
  exact
    GraphPath.cleanBetweenTerminalSets_internallyDisjointFromSet_union
      (B.routes.path p) (B.route_connects_side_row_unions p)

theorem sideChangingPath_stays
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.sideChangingPath p).vertexSet ⊆ C := by
  exact fun v hv =>
    B.routes_stay p (B.sideChangingPath_vertexSet_subset_route p hv)

theorem sideChangingPath_nodeDisjoint
    (B : PrescribedBisectionRouting R anchor U W C)
    {p q : B.routes.Index} (hpq : p ≠ q) :
    GraphPath.NodeDisjoint
      (B.sideChangingPath p) (B.sideChangingPath q) := by
  exact (B.routes.node_disjoint hpq).mono
    (B.sideChangingPath_vertexSet_subset_route p)
    (B.sideChangingPath_vertexSet_subset_route q)

/-- The suffix from the selected transition's right-side attachment to the
original, uniquely labelled route target.  Task B needs this provenance in
the hub branch. -/
noncomputable def routeSuffixFromTransition
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : GraphPath G :=
  (B.routes.path p).dropUntil
    (B.sideChangingPath_vertexSet_subset_route p
      (GraphPath.target_mem_vertexSet (B.sideChangingPath p)))

@[simp] theorem routeSuffixFromTransition_source
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routeSuffixFromTransition p).source =
      (B.sideChangingPath p).target := rfl

@[simp] theorem routeSuffixFromTransition_target
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routeSuffixFromTransition p).target =
      anchor (B.targetLabel p).1 := by
  rw [routeSuffixFromTransition, GraphPath.dropUntil_target,
    B.target_eq_anchor_targetLabel]

theorem routeSuffixFromTransition_vertexSet_subset_route
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.routeSuffixFromTransition p).vertexSet ⊆
      (B.routes.path p).vertexSet := by
  exact
    (B.routes.path p).dropUntil_vertexSet_subset
      (B.sideChangingPath_vertexSet_subset_route p
        (GraphPath.target_mem_vertexSet (B.sideChangingPath p)))

/-- The complete per-route transition record consumed by the occurrence
multigraph and hub-certificate stages. -/
structure SideChangingTransition
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) where
  original : B.LabelledRoute p
  leftRow : {r : R.Index // r ∈ U}
  rightRow : {r : R.Index // r ∈ W}
  path : GraphPath G
  routeSuffix : GraphPath G
  source_mem_leftRow :
    path.source ∈ (R.path leftRow.1).vertexSet
  target_mem_rightRow :
    path.target ∈ (R.path rightRow.1).vertexSet
  internallyDisjoint_activeRows :
    path.InternallyDisjointFromSet
      (selectedRowVertexSet R B.activeRows)
  vertexSet_subset_route :
    path.vertexSet ⊆ (B.routes.path p).vertexSet
  suffix_source : routeSuffix.source = path.target
  suffix_target :
    routeSuffix.target = anchor original.target.1
  suffix_vertexSet_subset_route :
    routeSuffix.vertexSet ⊆ (B.routes.path p).vertexSet

noncomputable def sideChangingTransition
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    B.SideChangingTransition p where
  original := B.labelledRoute p
  leftRow := B.transitionLeftRow p
  rightRow := B.transitionRightRow p
  path := B.sideChangingPath p
  routeSuffix := B.routeSuffixFromTransition p
  source_mem_leftRow :=
    B.sideChangingPath_source_mem_transitionLeftRow p
  target_mem_rightRow :=
    B.sideChangingPath_target_mem_transitionRightRow p
  internallyDisjoint_activeRows :=
    B.sideChangingPath_consecutive_active_contacts p
  vertexSet_subset_route :=
    B.sideChangingPath_vertexSet_subset_route p
  suffix_source := B.routeSuffixFromTransition_source p
  suffix_target := by
    simpa [labelledRoute] using B.routeSuffixFromTransition_target p
  suffix_vertexSet_subset_route :=
    B.routeSuffixFromTransition_vertexSet_subset_route p

theorem sideChangingTransition_nodeDisjoint
    (B : PrescribedBisectionRouting R anchor U W C)
    {p q : B.routes.Index} (hpq : p ≠ q) :
    GraphPath.NodeDisjoint
      (B.sideChangingTransition p).path
      (B.sideChangingTransition q).path := by
  exact B.sideChangingPath_nodeDisjoint hpq

end PrescribedBisectionRouting
end CutResponder
end Exponent7
end SimpleGraph
