import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import TwinWidth.Graph.Minor
import TwinWidth.Graph.Theorem46

/-!
# Contract for Chuzhoy--Tan Section 4.2

This contract records the main formal statements of Section 4.2 used by the
pseudo-grid branch.  The discard step producing `Q''`, property I1, the
row-support unique-linkage reduction, and the final slicing-minor outcome are
proved self-containedly in `PseudoGridSlicing.lean`.  The generic Theorem 4.6
is proved self-containedly in `Theorem46.lean`, using Lemma 4.5 from
`UniqueLinkageOrdering.lean`.
-/

namespace TwinWidth
namespace SimpleGraph

universe u

namespace PathSlicing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V}

/-- Chuzhoy--Tan Theorem 4.6: a unique linkage intersected by a sufficiently
large disjoint auxiliary path family admits an `M`-slicing of width at least
`w`. -/
theorem theorem46_contract
    (R : PerfectPathPacking G A B) (Qpack : PathPacking G S T)
    (M w : ℕ)
    (hM : 0 < M) (hw : 0 < w)
    (hunique : R.IsUniqueLinkage)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    (hcard : M * w + (M + 1) * R.card ≤ Qpack.card) :
    ∃ sigma : PathSlicing R M, sigma.WidthAtLeast Qpack w :=
  theorem46 R Qpack M w hM hw hunique hintersects hcard

end PathSlicing

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

omit [Fintype V] in
/-- Section 4.2, first paragraph: discarding the union of the row-bad sets
leaves a subfamily `Q''` of the requested size, and each retained path
intersects every row `R_i` of the pseudo-grid. -/
theorem section42_discard_bad_paths_contract
    (Gamma : PseudoGrid G A B X g D P Q) {m : ℕ}
    (hcard : D * (2 * g ^ 2) + m ≤ Fintype.card Gamma.QIndex) :
    ∃ Qgood : Finset Gamma.QIndex,
      m ≤ Qgood.card ∧
        ∀ j ∈ Qgood, ∀ i : Fin D,
          pseudoGridIntersectsRow P Gamma.reserved Gamma.qPath i j :=
  Gamma.section42_discard_bad_paths hcard

end PseudoGrid

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {g D M w : ℕ}
variable {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}

/-- Contract-labelled alias for the combined Section 4.2 outcome in the
pseudo-grid branch: under the cardinality hypothesis needed by Theorem 4.6, the
pseudo-grid produces a minor with a perfect unique linkage and an `M`-slicing of
width `w`. -/
theorem section42_slicing_minor_of_pseudoGrid_contract
    (Gamma : PseudoGrid G A B X g D P Q)
    (_hminimal : P.IsMinimumTheorem41Pair Q)
    (hM : 0 < M) (hw : 0 < w)
    (hcard :
      M * w + (M + 1) * Gamma.rowPacking.card ≤ Gamma.goodQSet.card) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (H : _root_.SimpleGraph W),
      ∃ (A' B' S T : Finset W),
        ∃ (R : PerfectPathPacking H A' B') (Qpack : PathPacking H S T),
          ∃ sigma : PathSlicing R M,
            IsMinor H G ∧
              R.IsUniqueLinkage ∧
                R.card = Gamma.rowPacking.card ∧
                  sigma.WidthAtLeast Qpack w := by
  exact Gamma.section42_slicing_minor_of_pseudoGrid _hminimal hM hw hcard

end PseudoGrid

end SimpleGraph
end TwinWidth
