import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma hasZeroEdgeDisjointSpanningTrees (G : MultiGraph V E) :
    G.HasKEdgeDisjointSpanningTrees 0 := by
  refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i _j _hij
    exact Fin.elim0 i

/-- The `k = 0` specialization of Diestel, Theorem 2.4.1. -/
theorem theorem_2_4_1_k_zero {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.Loopless →
      (G.HasKEdgeDisjointSpanningTrees 0 ↔
        ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
          0 * (P.card - 1) ≤ G.crossEdgeCount P) := by
  intro _hloopless
  constructor
  · intro _hpack P _hP
    simp
  · intro _hbound
    exact hasZeroEdgeDisjointSpanningTrees G

/-- The `k = 0` specialization of Diestel, Corollary 2.4.2. -/
theorem corollary_2_4_2_k_zero {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.Loopless →
      G.IsLEdgeConnected (2 * 0) →
        G.HasKEdgeDisjointSpanningTrees 0 := by
  intro _hloopless _hconn
  exact hasZeroEdgeDisjointSpanningTrees G

end MultiGraph

end Chapter02
end Diestel
