import «statements-and-proofs».Exponent8.Observation54Type2

/-!
# Observation 5.4 for one recursive-slicing layer

This module applies the graph-theoretic Observation 5.4 theorem to the
concrete additive cleanup and localization data stored in
`RecursiveSliceLayer`.

For one parent slice, the bad rows are the rows discarded by Lemma 4.8 and
the good auxiliary paths are the paths surviving the strengthened Claim 5.3
filter.  Membership in that filter proves that every good path avoids every
discarded row segment.  The positive `Dhat` lower bound in the additive
cleanup supplies an actual retained row met by each good path.

The resulting row and auxiliary packings live in the exact retained-row
support subtype.  Thus the output is a proof-producing, axiom-free version of
the type-two part of Chuzhoy--Tan Observation 5.4.
-/

namespace SimpleGraph
namespace Exponent8

universe u v

open Finset

namespace RecursiveSliceLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {m width wHat Dhat : ℕ}

/-- Rows discarded by additive Lemma 4.8 in one recursive slice. -/
noncomputable def observation54BadRows
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) : Finset Rbar.Index :=
  (Finset.univ : Finset Rbar.Index) \ (L.cleanup i).rows

/-- Auxiliary paths surviving deletion of every path meeting a discarded
row segment. -/
noncomputable def observation54GoodQ
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) : Finset Qbar.Index :=
  (L.localization i).goodQ
    (L.observation54BadRows i) (L.cleanup i).paths

theorem observation54GoodQ_subset
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :
    L.observation54GoodQ i ⊆ (L.cleanup i).paths :=
  (L.localization i).goodQ_subset
    (L.observation54BadRows i) (L.cleanup i).paths

/-- A good path cannot meet a row discarded by the cleanup.  Otherwise the
slice-local intersection would put that path in `badHitQ`, contradicting the
definition as a finite-set difference. -/
theorem observation54GoodQ_avoids_discarded
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :
    ∀ q ∈ L.observation54GoodQ i,
      ∀ r : Rbar.Index, r ∉ (L.cleanup i).rows →
        Disjoint (Qbar.path q).vertexSet
          (L.sigma.sliceRowPath i r).vertexSet := by
  classical
  intro q hq r hr
  rw [Finset.disjoint_left]
  intro z hzQ hzRow
  have hqCleanup : q ∈ (L.cleanup i).paths :=
    L.observation54GoodQ_subset i hq
  have hqSlice : q ∈ L.sigma.pathsInSlice Qbar i :=
    (L.cleanup i).paths_subset hqCleanup
  have hqLocalized : q ∈ (L.localization i).localizedQ := by
    rw [L.localized_eq i]
    exact hqCleanup
  have hsegment :
      L.sigma.SliceSegmentIntersectsPath Qbar i r q := by
    apply
      (L.sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
        Qbar hqSlice).2
    rw [PathPacking.PathsIntersect, Finset.not_disjoint_iff]
    exact ⟨z, hzRow, hzQ⟩
  have hrBad : r ∈ L.observation54BadRows i := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr⟩
  have hbad :
      q ∈ (L.localization i).badHitQ
        (L.observation54BadRows i) (L.cleanup i).paths := by
    apply
      ((L.localization i).mem_badHitQ
        (L.observation54BadRows i) (L.cleanup i).paths q).2
    exact ⟨hqCleanup, hqLocalized, ⟨r, hrBad, hsegment⟩⟩
  exact
    (Finset.mem_sdiff.mp
      (show
        q ∈ (L.cleanup i).paths \
          (L.localization i).badHitQ
            (L.observation54BadRows i) (L.cleanup i).paths
        from hq)).2 hbad

/-- Every good auxiliary path still meets a retained row.  This uses only
the positive `Dhat` side of the additive cleanup's intersecting certificate;
no cardinality is discarded in this conversion. -/
theorem observation54GoodQ_meets_retained
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (hDhat : 0 < Dhat) :
    ∀ q ∈ L.observation54GoodQ i,
      ∃ r ∈ (L.cleanup i).rows,
        L.sigma.SliceSegmentIntersectsPath Qbar i r q := by
  classical
  intro q hq
  have hqCleanup : q ∈ (L.cleanup i).paths :=
    L.observation54GoodQ_subset i hq
  have hdense :=
    (L.cleanup i).intersecting.2 q hqCleanup
  have hpositive :
      0 <
        (L.sigma.segmentIntersectingLeftIndices
          Qbar i (L.cleanup i).rows q).card :=
    lt_of_lt_of_le hDhat hdense
  rcases Finset.card_pos.mp hpositive with ⟨r, hr⟩
  rw [L.sigma.mem_segmentIntersectingLeftIndices] at hr
  exact ⟨r, hr.1, hr.2⟩

/-- The exact-support retained-row packing produced from one recursive
slice. -/
noncomputable def observation54Rows
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :=
  PathSlicing.retainedSliceRows
    L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
    (L.cleanup i).rows L.unique_linkage.1
    (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)

/-- The good auxiliary packing, induced onto the exact retained-row
support. -/
noncomputable def observation54Aux
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) :=
  PathSlicing.retainedSliceAux
    L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
    (L.cleanup i).rows L.unique_linkage
    (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)
    (L.observation54GoodQ_avoids_discarded i)

/-- Chuzhoy--Tan Observation 5.4, type-two branch, specialized to one
recursive layer.  This is the theorem consumed by the local Theorem 4.6
refinement: the rows are a perfect unique linkage, the auxiliary family
meets it, and neither family loses indices during the support transports. -/
theorem observation54_type2_cleaned_slice
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar m width wHat Dhat)
    (i : Fin m) (hDhat : 0 < Dhat) :
    (L.observation54Rows i).IsUniqueLinkage ∧
      (L.observation54Rows i).card = (L.cleanup i).rows.card ∧
      (L.observation54Aux i).card =
        (L.observation54GoodQ i).card ∧
      _root_.SimpleGraph.PathSlicing.PathPackingIntersectsLinkage
        (L.observation54Rows i) (L.observation54Aux i) := by
  simpa only [observation54Rows, observation54Aux] using
    (PathSlicing.observation54_type2_cleaned_slice
      L.sigma i (L.cleanup i).paths (L.observation54GoodQ i)
      (L.cleanup i).rows L.unique_linkage
      (L.cleanup i).paths_subset (L.observation54GoodQ_subset i)
      (L.observation54GoodQ_avoids_discarded i)
      (L.observation54GoodQ_meets_retained i hDhat))

end RecursiveSliceLayer
end Exponent8
end SimpleGraph
