import «statements-and-proofs».Exponent7.CutResponder.CrossingMatchingOrHub
import «statements-and-proofs».Exponent7.GlobalRowThreading

/-!
# The application-specific strong-cluster cut responder

This module states the minimal frontier requested by the cut-matching
application.  The active rows are named by `GridVertex g`, the cut is an
actual `CutMatchingGame.Bisection`, and the row paths are the exact local
traces of selected global rows in one cluster of a strong path-of-sets
system.

The current strong-system fields construct the labelled bisection routing and
prove the exact alternative

* a constant-fraction clean crossing batch; or
* the provenance-rich hub certificate from
  `CrossingMatchingOrHub`.

No project axiom is introduced.  A separate theorem below proves the desired
responder when the occurrence multiplicity at every active row is bounded.
This makes the remaining mathematical question precise: ordinary bounded
vertex degree does not itself bound the number of distinct attachment
vertices along a long selected row.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

variable {ell w g : ℕ}

/-- The local cluster-linkage index of a selected global row. -/
noncomputable def localGridRow
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index) :
    GridVertex g ↪
      (StrongPathOfSetsSystem.clusterLinkage P i).Index where
  toFun := fun x =>
    (GlobalRowPrefix.globalRows P).localIndex i
      (GlobalRowPrefix.index_le_last P i) (selected x)
  inj' :=
    ((GlobalRowPrefix.globalRows P).localIndex_injective i
      (GlobalRowPrefix.index_le_last P i)).comp selected.injective

theorem localGridRow_path_subset_global
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (x : GridVertex g) :
    ((StrongPathOfSetsSystem.clusterLinkage P i).path
      (localGridRow P i selected x)).vertexSet ⊆
        ((GlobalRowPrefix.globalRows P).packing.path
          (selected x)).vertexSet :=
  (GlobalRowPrefix.globalRows P).local_path_subset i
    (GlobalRowPrefix.index_le_last P i) (selected x)

variable {ell w g : ℕ}

/-- The selected local row indices on the left side of a grid-coordinate
bisection. -/
noncomputable def cutLeftLocalRows
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)) :
    Finset (StrongPathOfSetsSystem.clusterLinkage P i).Index :=
  cut.left.image (localGridRow P i selected)

/-- The selected local row indices on the right side of a grid-coordinate
bisection. -/
noncomputable def cutRightLocalRows
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)) :
    Finset (StrongPathOfSetsSystem.clusterLinkage P i).Index :=
  cut.right.image (localGridRow P i selected)

theorem cutLocalRows_disjoint
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)) :
    Disjoint
      (cutLeftLocalRows P i selected cut)
      (cutRightLocalRows P i selected cut) := by
  classical
  rw [Finset.disjoint_left]
  intro r hrL hrR
  rcases Finset.mem_image.mp hrL with ⟨x, hx, hxr⟩
  rcases Finset.mem_image.mp hrR with ⟨y, hy, hyr⟩
  have hxy : x = y :=
    (localGridRow P i selected).injective (hxr.trans hyr.symm)
  exact Finset.disjoint_left.mp cut.disjoint hx (by simpa [hxy] using hy)

theorem cutLocalRows_card_eq
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)) :
    (cutLeftLocalRows P i selected cut).card =
      (cutRightLocalRows P i selected cut).card := by
  classical
  rw [cutLeftLocalRows, cutRightLocalRows,
    Finset.card_image_of_injective, Finset.card_image_of_injective]
  · exact cut.card_eq
  · exact (localGridRow P i selected).injective
  · exact (localGridRow P i selected).injective

theorem cutLeftLocalRows_card
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)) :
    (cutLeftLocalRows P i selected cut).card = cut.left.card := by
  classical
  rw [cutLeftLocalRows, Finset.card_image_of_injective]
  exact (localGridRow P i selected).injective

/-- The canonical explicit routing between any two disjoint, equally sized
subsets of the selected grid rows.  This residual form is needed when a full
bisection is peeled in several fresh clusters. -/
noncomputable def strongClusterExplicitRouting
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (U W : Finset (GridVertex g))
    (hdisjoint : Disjoint U W)
    (hcard : U.card = W.card) :
    PrescribedBisectionRouting
      (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
      (fun r =>
        ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
      (U.image (localGridRow P i selected))
      (W.image (localGridRow P i selected))
      (P.cluster i) := by
  classical
  let R :=
    (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
  have hanchor :
      ∀ r : R.Index,
        (R.path r).source ∈ (R.path r).vertexSet :=
    fun r => GraphPath.source_mem_vertexSet _
  have hanchorSet :
      ((Finset.univ : Finset R.Index).image
          (fun r => (R.path r).source)) =
        P.left i := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨r, _hr, hrv⟩
      simpa [R, ← hrv] using
        (StrongPathOfSetsSystem.clusterLinkage P i).source_mem r
    · intro hv
      rcases
          (StrongPathOfSetsSystem.clusterLinkage P i).source_bijective.2
            ⟨v, hv⟩ with
        ⟨r, hr⟩
      refine Finset.mem_image.mpr ⟨r, Finset.mem_univ r, ?_⟩
      exact congrArg Subtype.val hr
  have hlocalDisjoint :
      Disjoint
        (U.image (localGridRow P i selected))
        (W.image (localGridRow P i selected)) := by
    rw [Finset.disjoint_left]
    intro r hrU hrW
    rcases Finset.mem_image.mp hrU with ⟨x, hx, hxr⟩
    rcases Finset.mem_image.mp hrW with ⟨y, hy, hyr⟩
    have hxy : x = y :=
      (localGridRow P i selected).injective
        (hxr.trans hyr.symm)
    exact Finset.disjoint_left.mp hdisjoint hx
      (by simpa [hxy] using hy)
  have hlocalCard :
      (U.image (localGridRow P i selected)).card =
        (W.image (localGridRow P i selected)).card := by
    rw [Finset.card_image_of_injective,
      Finset.card_image_of_injective]
    · exact hcard
    · exact (localGridRow P i selected).injective
    · exact (localGridRow P i selected).injective
  apply prescribedBisectionRouting
    R (fun r => (R.path r).source) hanchor
      (U.image (localGridRow P i selected))
      (W.image (localGridRow P i selected))
      (P.cluster i) hlocalDisjoint hlocalCard
  rw [hanchorSet]
  exact P.left_nodeWellLinked i

/-- The canonical explicit bisection routing in one strong cluster. -/
noncomputable def strongClusterBisectionRouting
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)) :
    PrescribedBisectionRouting
      (StrongPathOfSetsSystem.clusterLinkage P i).toPathPacking
      (fun r =>
        ((StrongPathOfSetsSystem.clusterLinkage P i).path r).source)
      (cutLeftLocalRows P i selected cut)
      (cutRightLocalRows P i selected cut)
      (P.cluster i) := by
  exact strongClusterExplicitRouting P i selected
    cut.left cut.right cut.disjoint cut.card_eq

/-- A response in one strong cluster.  Its transition family is explicitly
crossing, endpoint-disjoint, pairwise node-disjoint, and internally disjoint
from every active selected local row. -/
structure StrongClusterCrossingResponse
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g))
    (responseConstant : ℕ) where
  batch :
    PrescribedBisectionRouting.CrossingCleanBatch
      (strongClusterBisectionRouting P i selected cut)
  fraction :
    cut.left.card ≤ responseConstant * batch.card

/-- The application-specific theorem which would be sufficient for one
cut-matching response.  This is a proposition, not an axiom. -/
def StrongClusterCutResponderStatement
    (reserve responseConstant : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V)
    {ell w g : ℕ}
    (P : StrongPathOfSetsSystem G ell w)
    (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g)),
      MaxDegreeAtMost G 4 →
      2 ≤ g →
      reserve * g ^ 2 ≤ w →
      ContainsGridMinor G g ∨
        Nonempty
          (StrongClusterCrossingResponse
            P i selected cut responseConstant)

/-- What the current strong-cluster interface proves without an additional
hub-resolution theorem. -/
theorem strongCluster_crossingResponse_or_hubCertificate
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g))
    (responseConstant : ℕ) :
    Nonempty
        (StrongClusterCrossingResponse
          P i selected cut responseConstant) ∨
      Nonempty
        (PrescribedBisectionRouting.CrossingHubCertificate
          (strongClusterBisectionRouting P i selected cut)
          responseConstant) := by
  let B := strongClusterBisectionRouting P i selected cut
  rcases B.crossingMatching_or_hubCertificate responseConstant with
    hbatch | hhub
  · exact Or.inl
      ⟨{
        batch := B.maximumCrossingBatch
        fraction := by
          rw [← cutLeftLocalRows_card P i selected cut,
            ← B.routes_card]
          exact hbatch
      }⟩
  · exact Or.inr hhub

/-- The hub is resolved immediately if each active row has occurrence
multiplicity at most `d`.  This is the exact finite inequality used later:
the response constant is `2*d`. -/
theorem strongClusterCrossingResponse_of_occurrenceDegreeAtMost
    (P : StrongPathOfSetsSystem G ell w) (i : Fin ell)
    (selected :
      GridVertex g ↪
        (GlobalRowPrefix.globalRows P).packing.Index)
    (cut : CutMatchingGame.Bisection (GridVertex g))
    {d : ℕ}
    (hcapacity :
      PrescribedBisectionRouting.OccurrenceDegreeAtMost
        (strongClusterBisectionRouting P i selected cut) d) :
    Nonempty
      (StrongClusterCrossingResponse P i selected cut (2 * d)) := by
  let B := strongClusterBisectionRouting P i selected cut
  refine
    ⟨{
      batch := B.maximumCrossingBatch
      fraction := ?_
    }⟩
  rw [← cutLeftLocalRows_card P i selected cut, ← B.routes_card]
  exact B.routes_card_le_two_mul_degree_mul_maximumCrossingBatch hcapacity

end CutResponder
end Exponent7
end SimpleGraph
