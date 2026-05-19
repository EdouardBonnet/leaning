import TwinWidth.Graph.Flow
import TwinWidth.Graph.FlowIntegrality
import TwinWidth.Graph.Menger

/-!
# Contract for standard finite flow theorems

The Chekuri--Chuzhoy boosting theorem uses standard flow facts:

* cut-well-linked terminals support a unit path flow with bounded edge
  congestion;
* a valid vertex-capacitated flow of integer value yields the same number of
  node-disjoint paths.

The first item remains as the fractional max-flow/min-cut contract.  The second
item is now proved from finite vertex-Menger in `FlowIntegrality` and is
re-exported here with the old contract-shaped name.
-/

namespace TwinWidth
namespace SimpleGraph

universe u

open Finset

namespace FlowContract

/-- Max-flow/min-cut consequence for scaled cut-well-linked sets: equal-size
terminal subsets can route one unit from each source to a distinct target with
edge congestion at most `alphaDen / alphaNum`. -/
axiom scaledEdgeWellLinked_exists_unit_edgeCongestedFlow
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {Terminals S T : Finset V}
    {alphaNum alphaDen : ℕ}
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) :
    ∃ F : OrientedPathFlow G S T,
      F.IsUnitFlow ∧
        F.EdgeCongestionAtMost (scaledCongestion alphaNum alphaDen)

/-- Integral vertex-flow decomposition: a unit-vertex-capacity flow of value at
least `k` contains `k` pairwise vertex-disjoint source-to-target paths. -/
theorem unitVertexCapacityFlow_hasDisjointSTPaths
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {S T : Finset V} {k : ℕ}
    (hflow : OrientedPathFlow.HasUnitVertexCapacityValueAtLeast G S T k) :
    HasDisjointSTPaths G S T k :=
  FlowIntegrality.unitVertexCapacityFlow_hasDisjointSTPaths hflow

end FlowContract

end SimpleGraph
end TwinWidth
