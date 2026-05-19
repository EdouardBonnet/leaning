import TwinWidth.Graph.Section43

/-!
# Contract for Chuzhoy--Tan Section 4.3

This contract exposes only the main Section 4.3 statements in graph-theoretic
language: the definition of `(w,D)`-intersecting path-set pairs, Lemma 4.8, and
the one-slice extraction used after Theorem 4.6.
-/

namespace TwinWidth
namespace SimpleGraph

universe u

namespace PathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T S' T' : Finset V}

/-- Chuzhoy--Tan Lemma 4.8.  If every auxiliary path meets at least `2D` row
paths and the auxiliary family is large enough, then after discarding at most
half the auxiliary paths we obtain a `(w,D)`-intersecting pair; every discarded
row path meets at most `w` retained auxiliary paths. -/
theorem lemma48_contract
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    {w D : ℕ}
    (_hw : 0 < w) (hD : 0 < D)
    (hdense :
      ∀ q ∈ Qset, 2 * D ≤ (R.intersectingLeftIndices Q Rset q).card)
    (hcard : 2 * Rset.card * w ≤ D * Qset.card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
        Q' ⊆ Qset ∧
          IntersectingPathSetPair R Q R' Q' w D ∧
            Qset.card ≤ 2 * Q'.card ∧
              ∀ r ∈ Rset \ R',
                (R.intersectingRightIndices Q Q' r).card ≤ w :=
  exists_intersecting_path_subfamilies R Q Rset Qset hD hdense hcard

end PathPacking

namespace PathSlicing

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

/-- Section 4.3 for a single slicing layer.  Under the numerical and
intersection hypotheses of Lemma 4.8, one obtains retained row segments and
retained auxiliary paths forming a `(w,D)`-intersecting pair, while keeping at
least half the auxiliary paths in that slice. -/
theorem section43_slice_contract
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (_hw : 0 < w) (hD : 0 < D)
    (hdense :
      ∀ q ∈ sigma.pathsInSlice Qpack i,
        2 * D ≤
          (sigma.segmentIntersectingLeftIndices Qpack i
            (Finset.univ : Finset R.Index) q).card)
    (hcard :
      2 * (Fintype.card R.Index) * w ≤
        D * (sigma.pathsInSlice Qpack i).card) :
    ∃ rows : Finset R.Index, ∃ paths : Finset Qpack.Index,
      rows ⊆ Finset.univ ∧
        paths ⊆ sigma.pathsInSlice Qpack i ∧
          sigma.SliceIntersectingPathSetPair Qpack i rows paths w D ∧
            (sigma.pathsInSlice Qpack i).card ≤ 2 * paths.card ∧
              ∀ r ∈ (Finset.univ : Finset R.Index) \ rows,
                (sigma.segmentIntersectingRightIndices Qpack i paths r).card ≤ w := by
  let out := exists_slice_intersecting_subfamilies sigma Qpack i hD hdense hcard
  exact
    ⟨out.rows, out.paths, out.rows_subset, out.paths_subset,
      out.intersecting, out.half_paths, out.discarded_rows_sparse⟩

end PathSlicing

end SimpleGraph
end TwinWidth
