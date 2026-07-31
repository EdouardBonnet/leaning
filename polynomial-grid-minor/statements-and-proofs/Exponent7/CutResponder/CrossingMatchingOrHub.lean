import «statements-and-proofs».Exponent7.CutResponder.PrescribedBisectionRouting

/-!
# Crossing occurrence matching versus a provenance-rich hub certificate

The side-changing transition attached to a routed path is an occurrence edge
in a bipartite multigraph.  Its left endpoint is a row in the prescribed left
side and its right endpoint is a row in the prescribed right side.  Parallel
occurrences are retained because the edge type is the route-index type.

A maximum support-disjoint occurrence subfamily is already a clean crossing
batch.  If this batch is not a requested constant fraction of all routes,
maximality gives a small vertex cover of occurrence endpoints.  The second
output below records that cover together with an incident owner for every
route, the attachment order on every owner row, the original source and final
target labels, and the route suffix from the owner attachment to its final
target.

Unlike the old `hubPairConnector`, no two tails are paired in the hub branch.
In particular, this module never changes a crossing occurrence into a
same-side edge.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T : Finset V}

namespace PrescribedBisectionRouting

variable
    {R : PathPacking G S T} {anchor : R.Index → V}
    {U W : Finset R.Index} {C : Finset V}

/-- The bipartite vertex type of the occurrence multigraph.  Keeping the two
sides as a sum makes bipartiteness definitional. -/
abbrev CrossingVertex
    (_B : PrescribedBisectionRouting R anchor U W C) :=
  Sum {r : R.Index // r ∈ U} {r : R.Index // r ∈ W}

/-- Forget the bipartite tag and recover the underlying row index. -/
def crossingVertexRow
    (B : PrescribedBisectionRouting R anchor U W C) :
    B.CrossingVertex → R.Index
  | Sum.inl r => r.1
  | Sum.inr r => r.1

/-- The two bipartite endpoints of one side-changing route occurrence. -/
noncomputable def occurrenceSupport
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : Finset B.CrossingVertex :=
  {Sum.inl (B.transitionLeftRow p),
    Sum.inr (B.transitionRightRow p)}

@[simp] theorem occurrenceSupport_card
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.occurrenceSupport p).card = 2 := by
  classical
  simp [occurrenceSupport]

/-- A maximum endpoint-disjoint subfamily of route occurrences. -/
noncomputable def maximumCrossingMatching
    (B : PrescribedBisectionRouting R anchor U W C) :
    Finset B.routes.Index :=
  maximumSupportDisjointSubfamily B.occurrenceSupport Finset.univ

theorem maximumCrossingMatching_subset
    (B : PrescribedBisectionRouting R anchor U W C) :
    B.maximumCrossingMatching ⊆ Finset.univ :=
  (maximumSupportDisjointSubfamily_spec
    B.occurrenceSupport Finset.univ).1

theorem maximumCrossingMatching_endpoint_disjoint
    (B : PrescribedBisectionRouting R anchor U W C) :
    SupportDisjointFamily B.occurrenceSupport
      B.maximumCrossingMatching :=
  (maximumSupportDisjointSubfamily_spec
    B.occurrenceSupport Finset.univ).2.1

/-- The occurrence vertices saturated by the maximum crossing matching. -/
noncomputable def saturatedCrossingVertices
    (B : PrescribedBisectionRouting R anchor U W C) :
    Finset B.CrossingVertex :=
  supportFamilyUnion B.occurrenceSupport B.maximumCrossingMatching

theorem saturatedCrossingVertices_card_le
    (B : PrescribedBisectionRouting R anchor U W C) :
    B.saturatedCrossingVertices.card ≤
      2 * B.maximumCrossingMatching.card := by
  apply supportFamilyUnion_card_le
  intro p hp
  exact (B.occurrenceSupport_card p).le

/-- Maximality says every occurrence has an endpoint saturated by the maximum
matching. -/
theorem occurrence_meets_saturatedCrossingVertices
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    ∃ x ∈ B.occurrenceSupport p,
      x ∈ B.saturatedCrossingVertices := by
  classical
  obtain ⟨q, hq, hoverlap⟩ :=
    exists_support_overlap_maximum
      B.occurrenceSupport Finset.univ
      (Finset.mem_univ p)
      (by
        refine ⟨Sum.inl (B.transitionLeftRow p), ?_⟩
        simp [occurrenceSupport])
  rw [Finset.not_disjoint_iff] at hoverlap
  rcases hoverlap with ⟨x, hxp, hxq⟩
  exact
    ⟨x, hxp, Finset.mem_biUnion.mpr ⟨q, hq, hxq⟩⟩

/-- Choose one saturated occurrence endpoint as the owner of every route. -/
noncomputable def occurrenceOwner
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : B.CrossingVertex :=
  Classical.choose (B.occurrence_meets_saturatedCrossingVertices p)

theorem occurrenceOwner_mem_support
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    B.occurrenceOwner p ∈ B.occurrenceSupport p :=
  (Classical.choose_spec
    (B.occurrence_meets_saturatedCrossingVertices p)).1

theorem occurrenceOwner_mem_saturated
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    B.occurrenceOwner p ∈ B.saturatedCrossingVertices :=
  (Classical.choose_spec
    (B.occurrence_meets_saturatedCrossingVertices p)).2

/-- Route occurrences assigned to one saturated occurrence vertex. -/
noncomputable def hubFiber
    (B : PrescribedBisectionRouting R anchor U W C)
    (x : B.CrossingVertex) : Finset B.routes.Index :=
  Finset.univ.filter fun p => B.occurrenceOwner p = x

@[simp] theorem mem_hubFiber
    (B : PrescribedBisectionRouting R anchor U W C)
    (x : B.CrossingVertex) (p : B.routes.Index) :
    p ∈ B.hubFiber x ↔ B.occurrenceOwner p = x := by
  classical
  simp [hubFiber]

theorem routes_card_eq_sum_hubFibers
    (B : PrescribedBisectionRouting R anchor U W C) :
    B.routes.card =
      ∑ x ∈ B.saturatedCrossingVertices, (B.hubFiber x).card := by
  classical
  change
    (Finset.univ : Finset B.routes.Index).card =
      ∑ x ∈ B.saturatedCrossingVertices,
        ((Finset.univ : Finset B.routes.Index).filter
          (fun p => B.occurrenceOwner p = x)).card
  apply Finset.card_eq_sum_card_fiberwise
  intro p hp
  exact B.occurrenceOwner_mem_saturated p

/-- The attachment of an occurrence to a chosen incident bipartite vertex. -/
noncomputable def occurrenceAttachment
    (B : PrescribedBisectionRouting R anchor U W C)
    (x : B.CrossingVertex) (p : B.routes.Index) : V :=
  match x with
  | Sum.inl _ => (B.sideChangingPath p).source
  | Sum.inr _ => (B.sideChangingPath p).target

theorem occurrenceAttachment_mem_transition
    (B : PrescribedBisectionRouting R anchor U W C)
    (x : B.CrossingVertex) (p : B.routes.Index) :
    B.occurrenceAttachment x p ∈ (B.sideChangingPath p).vertexSet := by
  cases x <;> simp [occurrenceAttachment,
    GraphPath.source_mem_vertexSet, GraphPath.target_mem_vertexSet]

theorem occurrenceAttachment_mem_row_of_incident
    (B : PrescribedBisectionRouting R anchor U W C)
    (x : B.CrossingVertex) (p : B.routes.Index)
    (hx : x ∈ B.occurrenceSupport p) :
    B.occurrenceAttachment x p ∈
      (R.path (B.crossingVertexRow x)).vertexSet := by
  classical
  cases x with
  | inl r =>
      have hr : r = B.transitionLeftRow p := by
        simpa [occurrenceSupport] using hx
      simpa [occurrenceAttachment, crossingVertexRow, hr] using
        B.sideChangingPath_source_mem_transitionLeftRow p
  | inr r =>
      have hr : r = B.transitionRightRow p := by
        simpa [occurrenceSupport] using hx
      simpa [occurrenceAttachment, crossingVertexRow, hr] using
        B.sideChangingPath_target_mem_transitionRightRow p

theorem occurrenceAttachment_mem_ownerRow
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    B.occurrenceAttachment (B.occurrenceOwner p) p ∈
      (R.path
        (B.crossingVertexRow (B.occurrenceOwner p))).vertexSet :=
  B.occurrenceAttachment_mem_row_of_incident _ _
    (B.occurrenceOwner_mem_support p)

theorem occurrenceAttachment_mem_route
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    B.occurrenceAttachment (B.occurrenceOwner p) p ∈
      (B.routes.path p).vertexSet :=
  B.sideChangingPath_vertexSet_subset_route p
    (B.occurrenceAttachment_mem_transition _ p)

/-- The numerical position of an attachment on its owner row.  Within one
hub fiber this is an injective coordinate and hence records the exact
attachment order. -/
noncomputable def occurrenceAttachmentRank
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : ℕ :=
  (R.path (B.crossingVertexRow (B.occurrenceOwner p))).vertexIndex
    (B.occurrenceAttachment (B.occurrenceOwner p) p)

theorem occurrenceAttachment_injective
    (B : PrescribedBisectionRouting R anchor U W C) :
    Function.Injective
      (fun p : B.routes.Index =>
        B.occurrenceAttachment (B.occurrenceOwner p) p) := by
  intro p q hpq
  by_contra hpne
  exact Finset.disjoint_left.mp (B.sideChangingPath_nodeDisjoint hpne)
    (B.occurrenceAttachment_mem_transition (B.occurrenceOwner p) p)
    (by
      change
        B.occurrenceAttachment (B.occurrenceOwner p) p =
          B.occurrenceAttachment (B.occurrenceOwner q) q at hpq
      rw [hpq]
      exact
        B.occurrenceAttachment_mem_transition
          (B.occurrenceOwner q) q)

theorem occurrenceAttachmentRank_injective_on_hub
    (B : PrescribedBisectionRouting R anchor U W C)
    {p q : B.routes.Index}
    (howner : B.occurrenceOwner p = B.occurrenceOwner q)
    (hrank :
      B.occurrenceAttachmentRank p =
        B.occurrenceAttachmentRank q) :
    p = q := by
  have hpRow := B.occurrenceAttachment_mem_ownerRow p
  have hpSupport :
      B.occurrenceAttachment (B.occurrenceOwner p) p ∈
        (R.path
          (B.crossingVertexRow (B.occurrenceOwner p))).walk.support := by
    simpa [GraphPath.vertexSet] using hpRow
  have hAttach :
      B.occurrenceAttachment (B.occurrenceOwner p) p =
        B.occurrenceAttachment (B.occurrenceOwner q) q := by
    have hrank' :
        (R.path
            (B.crossingVertexRow (B.occurrenceOwner p))).vertexIndex
              (B.occurrenceAttachment (B.occurrenceOwner p) p) =
          (R.path
            (B.crossingVertexRow (B.occurrenceOwner p))).vertexIndex
              (B.occurrenceAttachment (B.occurrenceOwner q) q) := by
      simpa [occurrenceAttachmentRank, howner] using hrank
    exact (List.idxOf_inj hpSupport).mp hrank'
  exact B.occurrenceAttachment_injective hAttach

theorem occurrenceAttachment_before_iff_rank_le
    (B : PrescribedBisectionRouting R anchor U W C)
    {p q : B.routes.Index}
    (howner : B.occurrenceOwner p = B.occurrenceOwner q) :
    (R.path
        (B.crossingVertexRow (B.occurrenceOwner p))).Before
      (B.occurrenceAttachment (B.occurrenceOwner p) p)
      (B.occurrenceAttachment (B.occurrenceOwner q) q) ↔
        B.occurrenceAttachmentRank p ≤
          B.occurrenceAttachmentRank q := by
  constructor
  · intro hbefore
    have hle :=
      (GraphPath.before_iff_vertexIndex_le
        (R.path
          (B.crossingVertexRow (B.occurrenceOwner p)))).1 hbefore |>.2.2
    simpa [occurrenceAttachmentRank, howner] using hle
  · intro hle
    apply
      (GraphPath.before_iff_vertexIndex_le
        (R.path
          (B.crossingVertexRow (B.occurrenceOwner p)))).2
    refine
      ⟨B.occurrenceAttachment_mem_ownerRow p, ?_, ?_⟩
    · simpa [howner] using B.occurrenceAttachment_mem_ownerRow q
    · simpa [occurrenceAttachmentRank, howner] using hle

/-- The route suffix beginning at the owner attachment and ending at the
original, uniquely labelled right anchor. -/
noncomputable def ownerRouteSuffix
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) : GraphPath G :=
  (B.routes.path p).dropUntil (B.occurrenceAttachment_mem_route p)

@[simp] theorem ownerRouteSuffix_source
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.ownerRouteSuffix p).source =
      B.occurrenceAttachment (B.occurrenceOwner p) p := rfl

@[simp] theorem ownerRouteSuffix_target
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.ownerRouteSuffix p).target =
      anchor (B.targetLabel p).1 := by
  rw [ownerRouteSuffix, GraphPath.dropUntil_target,
    B.target_eq_anchor_targetLabel]

theorem ownerRouteSuffix_vertexSet_subset_route
    (B : PrescribedBisectionRouting R anchor U W C)
    (p : B.routes.Index) :
    (B.ownerRouteSuffix p).vertexSet ⊆
      (B.routes.path p).vertexSet :=
  (B.routes.path p).dropUntil_vertexSet_subset
    (B.occurrenceAttachment_mem_route p)

theorem ownerRouteSuffix_nodeDisjoint
    (B : PrescribedBisectionRouting R anchor U W C)
    {p q : B.routes.Index} (hpq : p ≠ q) :
    GraphPath.NodeDisjoint
      (B.ownerRouteSuffix p) (B.ownerRouteSuffix q) :=
  (B.routes.node_disjoint hpq).mono
    (B.ownerRouteSuffix_vertexSet_subset_route p)
    (B.ownerRouteSuffix_vertexSet_subset_route q)

/-- An endpoint-disjoint family of crossing occurrences.  All path and label
data are recovered from the side-changing transition indexed by `occurrence`.
-/
structure CrossingCleanBatch
    (B : PrescribedBisectionRouting R anchor U W C) where
  occurrence : Finset B.routes.Index
  endpoint_disjoint :
    SupportDisjointFamily B.occurrenceSupport occurrence

namespace CrossingCleanBatch

def card
    {B : PrescribedBisectionRouting R anchor U W C}
    (K : CrossingCleanBatch B) : ℕ :=
  K.occurrence.card

theorem path_nodeDisjoint
    {B : PrescribedBisectionRouting R anchor U W C}
    (K : CrossingCleanBatch B)
    {p q : {p : B.routes.Index // p ∈ K.occurrence}}
    (hpq : p ≠ q) :
    GraphPath.NodeDisjoint
      (B.sideChangingPath p.1) (B.sideChangingPath q.1) := by
  apply B.sideChangingPath_nodeDisjoint
  intro h
  exact hpq (Subtype.ext h)

theorem path_internallyDisjoint_activeRows
    {B : PrescribedBisectionRouting R anchor U W C}
    (K : CrossingCleanBatch B)
    (p : {p : B.routes.Index // p ∈ K.occurrence}) :
    (B.sideChangingPath p.1).InternallyDisjointFromSet
      (selectedRowVertexSet R B.activeRows) :=
  B.sideChangingPath_consecutive_active_contacts p.1

theorem left_right_cross
    {B : PrescribedBisectionRouting R anchor U W C}
    (K : CrossingCleanBatch B)
    (p : {p : B.routes.Index // p ∈ K.occurrence}) :
    (B.transitionLeftRow p.1).1 ∈ U ∧
      (B.transitionRightRow p.1).1 ∈ W :=
  ⟨(B.transitionLeftRow p.1).2, (B.transitionRightRow p.1).2⟩

end CrossingCleanBatch

/-- The maximum endpoint-disjoint occurrence family as a clean crossing
batch. -/
noncomputable def maximumCrossingBatch
    (B : PrescribedBisectionRouting R anchor U W C) :
    CrossingCleanBatch B where
  occurrence := B.maximumCrossingMatching
  endpoint_disjoint := B.maximumCrossingMatching_endpoint_disjoint

@[simp] theorem maximumCrossingBatch_card
    (B : PrescribedBisectionRouting R anchor U W C) :
    B.maximumCrossingBatch.card = B.maximumCrossingMatching.card := rfl

/-- The small-matching branch, retaining all information needed for a later
hub-resolution argument.  The fiber identity and the bound on `hubs` quantify
the loss incurred by deleting or reserving hub rows. -/
structure CrossingHubCertificate
    (B : PrescribedBisectionRouting R anchor U W C)
    (responseConstant : ℕ) where
  matching_small :
    responseConstant * B.maximumCrossingMatching.card < B.routes.card
  hubs : Finset B.CrossingVertex
  hubs_eq : hubs = B.saturatedCrossingVertices
  hubs_card_le :
    hubs.card ≤ 2 * B.maximumCrossingMatching.card
  owner : B.routes.Index → B.CrossingVertex
  owner_eq : owner = B.occurrenceOwner
  owner_mem_hubs : ∀ p, owner p ∈ hubs
  owner_incident : ∀ p, owner p ∈ B.occurrenceSupport p
  originalSourceLabel : B.routes.Index → {r : R.Index // r ∈ U}
  originalSourceLabel_eq : originalSourceLabel = B.sourceLabel
  originalSourceLabel_injective : Function.Injective originalSourceLabel
  finalTargetLabel : B.routes.Index → {r : R.Index // r ∈ W}
  finalTargetLabel_eq : finalTargetLabel = B.targetLabel
  finalTargetLabel_injective : Function.Injective finalTargetLabel
  attachment : B.routes.Index → V
  attachment_eq :
    attachment =
      fun p => B.occurrenceAttachment (B.occurrenceOwner p) p
  attachment_mem_ownerRow :
    ∀ p,
      attachment p ∈
        (R.path (B.crossingVertexRow (owner p))).vertexSet
  attachment_injective : Function.Injective attachment
  attachmentRank : B.routes.Index → ℕ
  attachmentRank_eq : attachmentRank = B.occurrenceAttachmentRank
  attachmentRank_injective_on_hub :
    ∀ {p q}, owner p = owner q →
      attachmentRank p = attachmentRank q → p = q
  routeSuffix : B.routes.Index → GraphPath G
  routeSuffix_eq : routeSuffix = B.ownerRouteSuffix
  routeSuffix_source : ∀ p, (routeSuffix p).source = attachment p
  routeSuffix_target :
    ∀ p, (routeSuffix p).target = anchor (finalTargetLabel p).1
  routeSuffix_vertexSet_subset_route :
    ∀ p, (routeSuffix p).vertexSet ⊆ (B.routes.path p).vertexSet
  routeSuffix_node_disjoint :
    Pairwise fun p q =>
      GraphPath.NodeDisjoint (routeSuffix p) (routeSuffix q)
  fiber_partition :
    B.routes.card =
      ∑ x ∈ hubs,
        ((Finset.univ : Finset B.routes.Index).filter
          (fun p => owner p = x)).card

/-- The canonical hub certificate obtained from the saturated vertices of a
maximum occurrence matching. -/
noncomputable def crossingHubCertificate
    (B : PrescribedBisectionRouting R anchor U W C)
    (responseConstant : ℕ)
    (hsmall :
      responseConstant * B.maximumCrossingMatching.card < B.routes.card) :
    CrossingHubCertificate B responseConstant where
  matching_small := hsmall
  hubs := B.saturatedCrossingVertices
  hubs_eq := rfl
  hubs_card_le := B.saturatedCrossingVertices_card_le
  owner := B.occurrenceOwner
  owner_eq := rfl
  owner_mem_hubs := B.occurrenceOwner_mem_saturated
  owner_incident := B.occurrenceOwner_mem_support
  originalSourceLabel := B.sourceLabel
  originalSourceLabel_eq := rfl
  originalSourceLabel_injective := B.sourceLabel_injective
  finalTargetLabel := B.targetLabel
  finalTargetLabel_eq := rfl
  finalTargetLabel_injective := B.targetLabel_injective
  attachment :=
    fun p => B.occurrenceAttachment (B.occurrenceOwner p) p
  attachment_eq := rfl
  attachment_mem_ownerRow := B.occurrenceAttachment_mem_ownerRow
  attachment_injective := B.occurrenceAttachment_injective
  attachmentRank := B.occurrenceAttachmentRank
  attachmentRank_eq := rfl
  attachmentRank_injective_on_hub := by
    intro p q howner hrank
    exact B.occurrenceAttachmentRank_injective_on_hub howner hrank
  routeSuffix := B.ownerRouteSuffix
  routeSuffix_eq := rfl
  routeSuffix_source := B.ownerRouteSuffix_source
  routeSuffix_target := B.ownerRouteSuffix_target
  routeSuffix_vertexSet_subset_route :=
    B.ownerRouteSuffix_vertexSet_subset_route
  routeSuffix_node_disjoint := by
    intro p q hpq
    exact B.ownerRouteSuffix_nodeDisjoint hpq
  fiber_partition := B.routes_card_eq_sum_hubFibers

/-- Exact crossing-matching/hub dichotomy.  The first branch is a clean
crossing batch containing at least a `1 / responseConstant` fraction in
division-free form.  The second branch retains a small saturated hub cover and
the full labelled-route provenance needed to resolve it. -/
theorem crossingMatching_or_hubCertificate
    (B : PrescribedBisectionRouting R anchor U W C)
    (responseConstant : ℕ) :
    B.routes.card ≤ responseConstant * B.maximumCrossingBatch.card ∨
      Nonempty (CrossingHubCertificate B responseConstant) := by
  by_cases hlarge :
      B.routes.card ≤ responseConstant * B.maximumCrossingMatching.card
  · exact Or.inl (by simpa using hlarge)
  · exact Or.inr
      ⟨B.crossingHubCertificate responseConstant (by omega)⟩

/-- A bound on the multiplicity with which side-changing transition
occurrences may attach to one active row.  This is the exact local property
missing from ordinary bounded graph degree: a long degree-three row may have
arbitrarily many distinct attachment vertices. -/
def OccurrenceDegreeAtMost
    (B : PrescribedBisectionRouting R anchor U W C) (d : ℕ) : Prop :=
  ∀ x : B.CrossingVertex,
    ((Finset.univ : Finset B.routes.Index).filter
      (fun p => x ∈ B.occurrenceSupport p)).card ≤ d

theorem hubFiber_card_le_of_occurrenceDegreeAtMost
    (B : PrescribedBisectionRouting R anchor U W C)
    {d : ℕ} (hdegree : B.OccurrenceDegreeAtMost d)
    (x : B.CrossingVertex) :
    (B.hubFiber x).card ≤ d := by
  apply le_trans (Finset.card_le_card ?_) (hdegree x)
  intro p hp
  have howner : B.occurrenceOwner p = x :=
    (B.mem_hubFiber x p).1 hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ p, by
      rw [← howner]
      exact B.occurrenceOwner_mem_support p⟩

/-- With attachment multiplicity at most `d`, the maximum crossing matching
contains at least a `1 / (2*d)` fraction of all routed occurrences, in
division-free form. -/
theorem routes_card_le_two_mul_degree_mul_maximumCrossingBatch
    (B : PrescribedBisectionRouting R anchor U W C)
    {d : ℕ} (hdegree : B.OccurrenceDegreeAtMost d) :
    B.routes.card ≤ (2 * d) * B.maximumCrossingBatch.card := by
  calc
    B.routes.card =
        ∑ x ∈ B.saturatedCrossingVertices,
          (B.hubFiber x).card :=
      B.routes_card_eq_sum_hubFibers
    _ ≤ ∑ _x ∈ B.saturatedCrossingVertices, d :=
      Finset.sum_le_sum fun x hx =>
        B.hubFiber_card_le_of_occurrenceDegreeAtMost hdegree x
    _ = B.saturatedCrossingVertices.card * d := by simp
    _ ≤ (2 * B.maximumCrossingMatching.card) * d :=
      Nat.mul_le_mul_right d B.saturatedCrossingVertices_card_le
    _ = (2 * d) * B.maximumCrossingBatch.card := by
      rw [maximumCrossingBatch_card]
      ring

end PrescribedBisectionRouting
end CutResponder
end Exponent7
end SimpleGraph
