import TwinWidth.Graph.Section46
import TwinWidth.Graph.Theorem214Contract

/-!
# Contract for Chuzhoy--Tan Section 4.6

This contract exposes the Section 4.6 conversion interface in standalone
mathematical form.  The paper's constant-factor conversion is the following
assembly statement together with the external Chekuri--Chuzhoy theorems that
produce the three certificate families for the restricted nails.

The second theorem is a fully self-contained weakening that follows only from
the definitions already present in this repository: every positive-width weak
path-of-sets system has a strong width-one restriction.

The full proofs are in `TwinWidth.Graph.Section46`.
-/

namespace TwinWidth
namespace SimpleGraph
namespace Section46

universe u

/-- Observation 4.19.  If a terminal set is edge-well-linked in a cluster, then
it satisfies the cut definition of `1`-well-linkedness in that cluster:
for every partition `X,Y` of the cluster, the number of crossing edges is at
least the smaller terminal side. -/
theorem observation419_edgeWellLinked_implies_oneWellLinked_contract
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {C T : Finset V}
    (h : EdgeWellLinkedIn G C T) :
    ScaledEdgeWellLinkedIn G C T 1 1 :=
  scaledEdgeWellLinkedIn_one_of_edgeWellLinkedIn h

/-- Chekuri--Chuzhoy boosting theorem used as Chuzhoy--Tan Theorem 4.20
(Chekuri--Chuzhoy Theorem 2.14),
stated in the repository's scaled cut-well-linkedness language.  If `T` has
`κ` terminals, is `alphaNum / alphaDen` cut-well-linked in the connected
cluster `C`, and the ambient graph has maximum degree at most `Δ ≥ 3`, then
`T` contains a node-well-linked subset of size at least
`⌊(3 * alphaNum * κ) / (10 * Δ * alphaDen)⌋`. -/
theorem theorem420_nodeWellLinkedBoosting_contract
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {C T : Finset V} {alphaNum alphaDen Δ κ : ℕ}
    (hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : ScaledEdgeWellLinkedIn G C T alphaNum alphaDen) :
    ∃ T' : Finset V,
      T' ⊆ T ∧
        (3 * alphaNum * κ) / (10 * Δ * alphaDen) ≤ T'.card ∧
          NodeWellLinkedIn G C T' :=
  ChekuriChuzhoy.theorem214_nodeWellLinkedSubset_contract
    (G := G) (C := C) (T := T) (alphaNum := alphaNum)
    (alphaDen := alphaDen) (Δ := Δ) (κ := κ)
    hcluster hdegree hDelta halpha_pos halpha_le hcard hwell

/-- Chekuri--Chuzhoy linkedness theorem used as Chuzhoy--Tan Theorem 4.21 in
the `α = 1` form supplied by Observation 4.19.  If two disjoint terminal sets
`T1,T2` are each node-well-linked, their union is edge-well-linked, and both
sides have size at least `κ`, then every equal-size pair of subsets
`T1' ⊆ T1`, `T2' ⊆ T2` of size at most `κ / (2 * Δ)` is linked.

The size upper bound is written without division:
`2 * Δ * |T1'| ≤ κ`. -/
theorem theorem421_linkedSubsets_contract
    {V : Type u} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}
    {C T1 T2 T1' T2' : Finset V} {Δ κ : ℕ}
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 0 < Δ)
    (hdisj : Disjoint T1 T2)
    (hT1card : κ ≤ T1.card)
    (hT2card : κ ≤ T2.card)
    (hwell : EdgeWellLinkedIn G C (T1 ∪ T2))
    (hT1node : NodeWellLinkedIn G C T1)
    (hT2node : NodeWellLinkedIn G C T2)
    (hT1' : T1' ⊆ T1)
    (hT2' : T2' ⊆ T2)
    (hcard_eq : T1'.card = T2'.card)
    (hsmall : 2 * Δ * T1'.card ≤ κ) :
    NodeLinkedIn G C T1' T2' :=
  theorem421_linkedSubsets_edgeWellLinked
    (G := G) (C := C) (T1 := T1) (T2 := T2)
    (T1' := T1') (T2' := T2') (Δ := Δ) (κ := κ)
    hdegree hDelta hdisj hT1card hT2card hwell
    hT1node hT2node hT1' hT2' hcard_eq hsmall

/-- Paper-shaped Section 4.6 assembly contract.  If selected nail subsets and
selected connector subpackings satisfy the endpoint/cardinality conditions and
the retained left/right nails are node-well-linked and linked in each cluster
(the fields of `StrongificationData`), then they form a strong path-of-sets
system of the retained width. -/
theorem section46_strongification_data_contract
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w w' : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (D : StrongificationData (G := G) (P := P.toPathOfSetsSystem) (w' := w')) :
    Nonempty (StrongPathOfSetsSystem G ell w') :=
  ⟨strong_pathOfSetsSystem_of_strongificationData P D⟩

/-- Section 4.6 conversion contract.  Let `P` be a weak path-of-sets system.
Choose a positive width `w' ≤ w` and restrict `P` to `w'` nails per side using
the canonical connector-preserving restriction.  If in every restricted
cluster the left nails are node-well-linked, the right nails are
node-well-linked, and the left/right nail pair is node-linked, then the
restricted system is a strong path-of-sets system of width `w'`.

In the paper, Theorems 4.20 and 4.21 provide these certificates at a
constant-factor value of `w'`. -/
theorem section46_restricted_certificates_contract
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w w' : ℕ} (P : WeakPathOfSetsSystem G ell w)
    (hpos : 0 < w') (hle : w' ≤ w)
    (left_nails_node_well_linked :
      ∀ i : Fin ell,
        NodeWellLinkedIn G
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).cluster i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).left i))
    (right_nails_node_well_linked :
      ∀ i : Fin ell,
        NodeWellLinkedIn G
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).cluster i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).right i))
    (left_right_nails_linked :
      ∀ i : Fin ell,
        NodeLinkedIn G
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).cluster i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).left i)
          ((P.toPathOfSetsSystem.restrictWidth hpos hle).right i)) :
    Nonempty (StrongPathOfSetsSystem G ell w') :=
  ⟨strong_pathOfSetsSystem_of_restrictWidth_certificates P hpos hle
      left_nails_node_well_linked
      right_nails_node_well_linked
      left_right_nails_linked⟩

/-- Self-contained Section 4.6 weakening.  Every weak path-of-sets system of
positive width contains, by restricting to one connector/nail on each side, a
strong path-of-sets system of the same length and width one. -/
theorem section46_width_one_contract
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {ell w : ℕ} (P : WeakPathOfSetsSystem G ell w) (hw : 0 < w) :
    Nonempty (StrongPathOfSetsSystem G ell 1) :=
  weak_pathOfSetsSystem_to_strong_width_one P hw

end Section46
end SimpleGraph
end TwinWidth
