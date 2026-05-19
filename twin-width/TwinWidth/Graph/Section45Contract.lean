import TwinWidth.Graph.Section45

/-!
# Contract for Chuzhoy--Tan Section 4.5

This contract exposes the two main Section 4.5 statements in readable form:

* Theorem 4.15 in its numerical row-set form; and
* the graph assembly theorem that turns the selected slices, nails, and
  connector paths into a weak path-of-sets system.

The full proofs are in `TwinWidth.Graph.Section45`.
-/

namespace TwinWidth
namespace SimpleGraph
namespace Section45

universe u

/-- Chuzhoy--Tan Theorem 4.15.  Given `M` subsets of `[N]`, each of size at
least `D`, with `N ≥ 3w`, `D^2 ≥ 4Nw`, and `MD ≥ 2Nw`, there are `w`
increasing slice indices whose consecutive row sets overlap in at least `w`
rows.  The output is written as a list whose `List.IsChain` relation contains
both the strict increase and the overlap lower bound. -/
theorem theorem415_contract
    {N M D w : ℕ} (S : Fin M → Finset (Fin N))
    (hN : 3 * w ≤ N)
    (hDsq : 4 * N * w ≤ D ^ 2)
    (hlarge : 2 * N * w ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (S i).card) :
    ∃ l : List (Fin M),
      l.length = w ∧
        l.IsChain (LargeOverlapRel S w) :=
  theorem415 S hN hDsq hlarge hcard

/-- Section 4.5 graph assembly in row-endpoint form.  Given retained row sets
`S_i`, clusters `C_i`, endpoint maps from rows into each cluster, the paper's
row choices `T₁ ⊆ S_{i₁}` and `T_{j+1} ⊆ S_{i_j} ∩ S_{i_{j+1}}`, perfect
connector packings between consecutive endpoint sets, and weak well-linkedness
of each chosen nail union, construct a weak path-of-sets system of length and
width `w`.

This is a standalone contract statement for the paper's final Section 4.5
construction: the nail sets are the endpoint images of the selected row
subsets, and `List.IsChain (LargeOverlapRel sliceRows w)` is the formal
version of the chosen increasing slice sequence with overlaps of size at least
`w`. -/
theorem section45_weak_pathOfSetsSystem_contract
    {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {N M D w : ℕ}
    (sliceRows : Fin M → Finset (Fin N))
    (hwidth : 0 < w)
    (hN : 3 * w ≤ N)
    (hDsq : 4 * N * w ≤ D ^ 2)
    (hlarge : 2 * N * w ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (sliceRows i).card)
    (cluster : Fin M → Finset V)
    (cluster_connected : ∀ i : Fin M, IsCluster G (cluster i))
    (selected_cluster_disjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (_ : l.IsChain (LargeOverlapRel sliceRows w))
        ⦃i j : Fin w⦄, i ≠ j →
          Disjoint (cluster (selectedIndex l hlen i))
            (cluster (selectedIndex l hlen j)))
    (leftEndpoint rightEndpoint : Fin M → Fin N → V)
    (leftEndpoint_injective :
      ∀ i : Fin M, Function.Injective (leftEndpoint i))
    (rightEndpoint_injective :
      ∀ i : Fin M, Function.Injective (rightEndpoint i))
    (leftEndpoint_mem :
      ∀ (i : Fin M) {r : Fin N}, r ∈ sliceRows i →
        leftEndpoint i r ∈ cluster i)
    (rightEndpoint_mem :
      ∀ (i : Fin M) {r : Fin N}, r ∈ sliceRows i →
        rightEndpoint i r ∈ cluster i)
    (firstRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) → Finset (Fin N))
    (gapRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          (i : Fin w) → i.1 + 1 < w → Finset (Fin N))
    (firstRows_subset :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)),
          firstRows l hlen hchain ⊆
            sliceRows (selectedIndex l hlen ⟨0, hwidth⟩))
    (firstRows_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)),
          (firstRows l hlen hchain).card = w)
    (gapRows_subset_left :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          gapRows l hlen hchain i hi ⊆
            sliceRows (selectedIndex l hlen i))
    (gapRows_subset_right :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          gapRows l hlen hchain i hi ⊆
            sliceRows (selectedIndex l hlen ⟨i.1 + 1, hi⟩))
    (gapRows_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          (gapRows l hlen hchain i hi).card = w)
    (nails_disjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          Disjoint
            ((paperLeftRows firstRows gapRows l hlen hchain i).image
              (leftEndpoint (selectedIndex l hlen i)))
            ((paperRightRows firstRows gapRows l hlen hchain i).image
              (rightEndpoint (selectedIndex l hlen i))))
    (connector :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          PerfectPathPacking G
            ((paperRightRows firstRows gapRows l hlen hchain i).image
              (rightEndpoint (selectedIndex l hlen i)))
            ((paperLeftRows firstRows gapRows l hlen hchain ⟨i.1 + 1, hi⟩).image
              (leftEndpoint (selectedIndex l hlen ⟨i.1 + 1, hi⟩))))
    (connector_internally_disjoint_clusters :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w) (j : Fin w),
          (connector l hlen hchain i hi).toPathPacking.InternallyDisjointFromSet
            (cluster (selectedIndex l hlen j)))
    (connector_mutually_nodeDisjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        ⦃i j : Fin w⦄ (hi : i.1 + 1 < w) (hj : j.1 + 1 < w),
          i ≠ j →
            (connector l hlen hchain i hi).toPathPacking.MutuallyNodeDisjoint
              (connector l hlen hchain j hj).toPathPacking)
    (nails_weakWellLinked :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          EndpointRowsWeakWellLinked G cluster leftEndpoint rightEndpoint
            (selectedIndex l hlen i)
            (paperLeftRows firstRows gapRows l hlen hchain i)
            (paperRightRows firstRows gapRows l hlen hchain i) w) :
    Nonempty (WeakPathOfSetsSystem G w w) :=
  section45_weak_pathOfSetsSystem_of_paperRowEndpointData
    sliceRows hwidth hN hDsq hlarge hcard
    cluster cluster_connected selected_cluster_disjoint
    leftEndpoint rightEndpoint leftEndpoint_injective rightEndpoint_injective
    leftEndpoint_mem rightEndpoint_mem firstRows gapRows
    firstRows_subset firstRows_card
    gapRows_subset_left gapRows_subset_right gapRows_card
    nails_disjoint connector connector_internally_disjoint_clusters
    connector_mutually_nodeDisjoint nails_weakWellLinked

end Section45
end SimpleGraph
end TwinWidth
