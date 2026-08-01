import «statements-and-proofs».Exponent7.CutResponder.CleanResidualResponderV2
import «statements-and-proofs».PseudoGridReduction

/-!
# A finite descent over candidate bisection routings

The existential-routing interface permits choosing a linkage adapted to the
selected global rows.  We order candidate routings lexicographically by

1. the total number of selected local rows met by their routes; and
2. the total number of route edges.

The single natural-number measure below implements that order.  Its
coefficient is one larger than a uniform bound on the total route length.
Consequently any strict contact-count decrease wins regardless of the new
route lengths.

The final theorem proves that a rerouting-or-grid improvement lemma implies
the V2 responder by strong induction.  The improvement lemma remains an
ordinary proposition parameter; no axiom is declared.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {ell w g : ℕ}

/-- All local cluster-linkage rows corresponding to the selected global
`GridVertex` rows. -/
noncomputable def allSelectedLocalRows
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index) :
    Finset (StrongPathOfSetsSystem.clusterLinkage P i).Index :=
  (Finset.univ : Finset (GridVertex g)).image
    (localGridRow P i selected)

/-- Selected local rows met by one route.  This counts row labels, not the
number of contact vertices. -/
noncomputable def routeSelectedRows
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    {U W : Finset (GridVertex g)}
    (B :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i))
    (q : B.routes.Index) :
    Finset (StrongPathOfSetsSystem.clusterLinkage P i).Index :=
  (allSelectedLocalRows P i selected).filter fun r =>
    ¬ Disjoint
      (B.routes.path q).vertexSet
      ((StrongPathOfSetsSystem.clusterLinkage P i).path r).vertexSet

/-- Primary part of the routing measure: total selected-row incidence over
all routed paths. -/
noncomputable def routingContactCount
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    {U W : Finset (GridVertex g)}
    (B :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i)) : ℕ :=
  ∑ q : B.routes.Index,
    (routeSelectedRows P i selected B q).card

/-- Secondary part of the routing measure: total number of route edges. -/
noncomputable def routingTotalLength
    {S T : Finset V} (B : PerfectPathPacking G S T) : ℕ :=
  ∑ q : B.Index, (B.path q).edgeSet.card

/-- One route has at most `|V|` edges. -/
theorem GraphPath.edgeSet_card_le_fintypeCard
    (Q : GraphPath G) :
    Q.edgeSet.card ≤ Fintype.card V := by
  have hpath :=
    Section4Reduction.GraphPath.edgeSet_card_add_one_eq_vertexSet_card Q
  have hvertices := Finset.card_le_univ Q.vertexSet
  omega

/-- Uniform upper bound used as the base of the lexicographic encoding. -/
theorem routingTotalLength_le
    {S T : Finset V} (B : PerfectPathPacking G S T) :
    routingTotalLength B ≤ B.card * Fintype.card V := by
  classical
  rw [routingTotalLength]
  calc
    (∑ q : B.Index, (B.path q).edgeSet.card) ≤
        ∑ _q : B.Index, Fintype.card V := by
      exact Finset.sum_le_sum fun _q _hq =>
        GraphPath.edgeSet_card_le_fintypeCard (B.path _q)
    _ = B.card * Fintype.card V := by
      simp [PerfectPathPacking.card, Finset.sum_const]

/-- Natural-number encoding of lexicographic minimization by selected-row
contacts and then route length. -/
noncomputable def routingMeasure
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    {U W : Finset (GridVertex g)}
    (B :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i)) : ℕ :=
  (B.routes.card * Fintype.card V + 1) *
      routingContactCount P i selected B +
    routingTotalLength B.routes

/-- Candidate routings for the same bisection all have the same number of
routes. -/
theorem candidateRouting_card_eq
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    {U W : Finset (GridVertex g)}
    (B B' :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i)) :
    B'.routes.card = B.routes.card := by
  rw [B'.routes_card, B.routes_card]

/-- A strict contact-count decrease strictly decreases `routingMeasure`, no
matter how the individual route lengths change. -/
theorem routingMeasure_lt_of_contactCount_lt
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    {U W : Finset (GridVertex g)}
    (B B' :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i))
    (hcontact :
      routingContactCount P i selected B' <
        routingContactCount P i selected B) :
    routingMeasure P i selected B' <
      routingMeasure P i selected B := by
  let bound := B.routes.card * Fintype.card V
  have hcardRoutes : B'.routes.card = B.routes.card :=
    candidateRouting_card_eq P i selected B B'
  have hlength : routingTotalLength B'.routes ≤ bound := by
    simpa [bound, hcardRoutes] using routingTotalLength_le B'.routes
  have hcontactSucc :
      routingContactCount P i selected B' + 1 ≤
        routingContactCount P i selected B :=
    Nat.succ_le_iff.mpr hcontact
  rw [routingMeasure, routingMeasure, hcardRoutes]
  calc
    (bound + 1) * routingContactCount P i selected B' +
          routingTotalLength B'.routes ≤
        (bound + 1) * routingContactCount P i selected B' + bound :=
      Nat.add_le_add_left hlength _
    _ < (bound + 1) * routingContactCount P i selected B' +
          (bound + 1) := by
      exact Nat.add_lt_add_left (Nat.lt_succ_self bound) _
    _ = (bound + 1) *
          (routingContactCount P i selected B' + 1) := by ring
    _ ≤ (bound + 1) * routingContactCount P i selected B :=
      Nat.mul_le_mul_left _ hcontactSucc
    _ ≤ (bound + 1) * routingContactCount P i selected B +
          routingTotalLength B.routes :=
      Nat.le_add_right _ _

/-- If the contact count is unchanged, a strict total-length decrease is the
secondary decrease of `routingMeasure`. -/
theorem routingMeasure_lt_of_contactCount_eq_of_totalLength_lt
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    {U W : Finset (GridVertex g)}
    (B B' :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i))
    (hcontact :
      routingContactCount P i selected B' =
        routingContactCount P i selected B)
    (hlength :
      routingTotalLength B'.routes < routingTotalLength B.routes) :
    routingMeasure P i selected B' <
      routingMeasure P i selected B := by
  have hcardRoutes : B'.routes.card = B.routes.card :=
    candidateRouting_card_eq P i selected B B'
  rw [routingMeasure, routingMeasure, hcardRoutes, hcontact]
  exact Nat.add_lt_add_left hlength _

/-- The sole mathematical frontier after correcting the routing interface:
a fixed bad candidate routing either already forces the target grid or can be
replaced by a strictly smaller routing between the same terminal sets. -/
def StrongClusterRoutingImprovementStatement
    (reserve responseConstant : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    {ell w g : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card)
    (B :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i)),
      MaxDegreeAtMost G 4 →
      2 ≤ g →
      reserve * g ^ 2 ≤ w →
      ¬ Nonempty
          (StrongClusterCleanActiveCrossingResponseFor
            P i selected U W hdisjoint hcard B responseConstant) →
      ContainsGridMinor G g ∨
        ∃ B' :
          PrescribedBisectionRouting
            (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
            (fun r =>
              ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
            (U.image (localGridRow P i selected))
            (W.image (localGridRow P i selected))
            (P.cluster i),
          routingMeasure P i selected B' <
            routingMeasure P i selected B

/-- Package a clean response for a fixed routing as the existential V2
response. -/
def StrongClusterCleanActiveCrossingResponseFor.toV2
    {P : StrongPathOfSetsSystem G ell w} {i : Fin ell}
    {selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index}
    {U W : Finset (GridVertex g)}
    {hdisjoint : Disjoint U W}
    {hcard : U.card = W.card}
    {B :
      PrescribedBisectionRouting
        (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
        (fun r =>
          ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected))
        (P.cluster i)}
    {responseConstant : ℕ}
    (K : StrongClusterCleanActiveCrossingResponseFor
      P i selected U W hdisjoint hcard B responseConstant) :
    StrongClusterCleanActiveCrossingResponseV2
      P i selected U W hdisjoint hcard responseConstant where
  routing := B
  batch := K.batch
  fraction := K.fraction
  internallyDisjoint_allSelected := K.internallyDisjoint_allSelected

/-- Strong induction on `routingMeasure` converts the local improvement
lemma into the existential-routing cut responder. -/
theorem strongClusterCleanActiveCutResponderV2_of_routingImprovement
    {reserve responseConstant : ℕ}
    (himprove :
      StrongClusterRoutingImprovementStatement.{u}
        reserve responseConstant) :
    StrongClusterCleanActiveCutResponderStatementV2.{u}
      reserve responseConstant := by
  intro V _ _ G ell w g P i selected U W hdisjoint hcard
      hdegree hg hwidth
  let B0 :=
    strongClusterExplicitRouting
      P i selected U W hdisjoint hcard
  have descend :
      ∀ n : ℕ,
        (∀ B :
          PrescribedBisectionRouting
            (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
            (fun r =>
              ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
            (U.image (localGridRow P i selected))
            (W.image (localGridRow P i selected))
            (P.cluster i),
          routingMeasure P i selected B = n →
          ContainsGridMinor G g ∨
            Nonempty
              (StrongClusterCleanActiveCrossingResponseV2
                P i selected U W hdisjoint hcard responseConstant)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro B hmeasure
        by_cases hresponse :
            Nonempty
              (StrongClusterCleanActiveCrossingResponseFor
                P i selected U W hdisjoint hcard B responseConstant)
        · rcases hresponse with ⟨K⟩
          exact Or.inr ⟨K.toV2⟩
        · rcases himprove G P i selected U W hdisjoint hcard B
              hdegree hg hwidth hresponse with
            hgrid | ⟨B', hlt⟩
          · exact Or.inl hgrid
          · apply ih (routingMeasure P i selected B')
              (by simpa [hmeasure] using hlt) B' rfl
  exact descend (routingMeasure P i selected B0) B0 rfl

end CutResponder
end Exponent7
end SimpleGraph
