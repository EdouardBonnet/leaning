import «statements-and-proofs».Flow
import «statements-and-proofs».FlowWellLinked
import «statements-and-proofs».FlowIntegrality
import «statements-and-proofs».Menger

/-!
# Re-exported finite flow theorems

The Chekuri--Chuzhoy boosting theorem uses standard flow facts:

* scaled cut-well-linked terminals contain many disjoint paths in bounded
  degree graphs;
* a valid vertex-capacitated flow of integer value yields the same number of
  node-disjoint paths.

Both are now theorem wrappers over the self-contained finite max-flow/Menger
development.  This file intentionally introduces no flow axiom.
-/

namespace SimpleGraph

universe u

open Finset

namespace FlowContract

/-- Equal-size terminal subsets of a scaled cut-well-linked set contain many
node-disjoint paths in a bounded-degree graph.

The size bound is written without division:
`10 * Δ * alphaDen * k ≤ 3 * alphaNum * |S|`. -/
theorem scaledEdgeWellLinked_hasDisjointSTPaths
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {Terminals S T : Finset V}
    {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card)
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k :=
  FlowWellLinked.hasDisjointSTPaths_of_scaledEdgeWellLinked
    (G := G) (Terminals := Terminals) (S := S) (T := T)
    (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
    hdegree hDelta hwell hS hT hcard hk

/-- Sharpened disjoint-terminal version of the scaled cut-well-linked routing
theorem.

The size bound is written without division:
`5 * Δ * alphaDen * k ≤ 6 * alphaNum * |S|`. -/
theorem scaledEdgeWellLinked_hasDisjointSTPaths_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {Terminals S T : Finset V}
    {alphaNum alphaDen Δ k : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : ScaledEdgeWellLinked G Terminals alphaNum alphaDen)
    (hS : S ⊆ Terminals) (hT : T ⊆ Terminals)
    (hcard : S.card = T.card) (hdisj : Disjoint S T)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * S.card) :
    HasDisjointSTPaths G S T k :=
  FlowWellLinked.hasDisjointSTPaths_of_scaledEdgeWellLinked_disjoint
    (G := G) (Terminals := Terminals) (S := S) (T := T)
    (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
    hdegree hDelta hwell hS hT hcard hdisj hk

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
