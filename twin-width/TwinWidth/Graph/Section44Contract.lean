import TwinWidth.Graph.Section44

/-!
# Contract for Chuzhoy--Tan Section 4.4

This contract exposes the main Section 4.4 statements in graph-theoretic
language: Observation 4.9, Observation 4.10, and Theorem 4.11.  The full file
contains the exact weak edge-well-linked definition, the finite edge-boundary
language for Observation 4.10, the splitting/decomposition bookkeeping, and
self-contained proofs of the statements exposed here.
-/

namespace TwinWidth
namespace SimpleGraph
namespace Section44

universe u

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Observation 4.9.  If `|T| ≤ 2w`, weak `w`-well-linkedness implies ordinary
edge-well-linkedness. -/
theorem observation49_contract
    {C T : Finset V} {w : ℕ}
    (hcard : T.card ≤ 2 * w)
    (hweak : WeakEdgeWellLinkedIn G C T w) :
    EdgeWellLinkedIn G C T :=
  observation49 hcard hweak

/-- Observation 4.10.  If a terminal set is not weakly well-linked in a finite
cluster, then the cluster has a sparse terminal cut. -/
theorem observation410_contract :
    Observation410Statement :=
  observation410

namespace PathPacking

/-- Chuzhoy--Tan Theorem 4.11.  If two node-disjoint path families `Σ` and
`Q` are `(4w,2D)`-intersecting and `D ≥ 8w`, then a disjoint collection of
happy clusters retains at least a quarter of the `Σ`-paths. -/
theorem theorem411_contract :
    Theorem411Statement.{u} :=
  theorem411

end PathPacking

end Section44
end SimpleGraph
end TwinWidth
