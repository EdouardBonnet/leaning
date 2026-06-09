import Chapter02.tree_packing_glue_aux
import Chapter02.tree_packing_k_zero_aux
import Chapter02.tree_packing_k_one_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma hasKEdgeDisjointSpanningTrees_of_vertexSet_eq_empty
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ)
    (hV : G.vertexSet = ∅) :
    G.HasKEdgeDisjointSpanningTrees k := by
  refine ⟨fun _ : Fin k => (∅ : Set E), ?_, ?_⟩
  · intro _
    exact empty_isSpanningTree_of_vertexSet_eq_empty (G := G) hV
  · intro i j _hij
    rw [Set.disjoint_left]
    simp

lemma connected_of_partition_bound_pos
    {G : MultiGraph V E} [Finite E] {k : ℕ}
    (hk : 0 < k) (hne : G.vertexSet.Nonempty)
    (hbound : ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
      k * (P.card - 1) ≤ G.crossEdgeCount P) :
    G.Connected := by
  refine connected_of_partition_bound_one (G := G) hne ?_
  intro P hP
  have hb := hbound P hP
  have hle : 1 * (P.card - 1) ≤ k * (P.card - 1) := by
    simpa [one_mul] using
      Nat.mul_le_mul_right (P.card - 1) (Nat.succ_le_of_lt hk)
  exact hle.trans hb

lemma hasKEdgeDisjointSpanningTrees_of_partition_bound_of_packingCovering
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ)
    (hLoopless : G.Loopless)
    (hBC : G.Connected →
      ∃ P : Finset (Set V), G.PackingCoveringPartition P k)
    (hbound : ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
      k * (P.card - 1) ≤ G.crossEdgeCount P) :
    G.HasKEdgeDisjointSpanningTrees k := by
  classical
  by_cases hk : k = 0
  · subst k
    exact hasZeroEdgeDisjointSpanningTrees G
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    by_cases hV : G.vertexSet = ∅
    · exact hasKEdgeDisjointSpanningTrees_of_vertexSet_eq_empty G k hV
    · have hVne : G.vertexSet.Nonempty := Set.nonempty_iff_ne_empty.mpr hV
      have hconn : G.Connected :=
        connected_of_partition_bound_pos (G := G) hkpos hVne hbound
      rcases hBC hconn with ⟨P, hPack⟩
      exact packingCoveringPartition_hasKEdgeDisjointSpanningTrees_of_partition_bound
        (G := G) (P := P) (k := k) hVne hPack (hbound P hPack.1)

lemma theorem_2_4_1_of_packingCoveringTheorem
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ)
    (hBC : G.Loopless → G.Connected →
      ∃ P : Finset (Set V), G.PackingCoveringPartition P k) :
    G.Loopless →
      (G.HasKEdgeDisjointSpanningTrees k ↔
        ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
          k * (P.card - 1) ≤ G.crossEdgeCount P) := by
  intro hLoopless
  constructor
  · intro hpack P hP
    exact theorem_2_4_1_forward (G := G) k hpack P hP
  · intro hbound
    exact hasKEdgeDisjointSpanningTrees_of_partition_bound_of_packingCovering
      (G := G) (k := k) hLoopless (hBC hLoopless) hbound

end MultiGraph

end Chapter02
end Diestel
