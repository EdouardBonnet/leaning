import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma hasZeroEdgeDisjointSpanningTreesOn (G : MultiGraph V E) (U : Set V) :
    G.HasKEdgeDisjointSpanningTreesOn U 0 := by
  refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i _j _hij
    exact Fin.elim0 i

lemma single_vertexSet_partition {G : MultiGraph V E}
    (hVne : G.vertexSet.Nonempty) :
    IsVertexPartitionOf G.vertexSet ({G.vertexSet} : Finset (Set V)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    have hUeq : U = G.vertexSet := by simpa using hU
    subst U
    exact ⟨hVne, subset_rfl⟩
  · intro U hU W hW hne
    have hUeq : U = G.vertexSet := by simpa using hU
    have hWeq : W = G.vertexSet := by simpa using hW
    exact False.elim (hne (hUeq.trans hWeq.symm))
  · intro v hv
    exact ⟨G.vertexSet, by simp, hv⟩

lemma no_crossEdge_single_vertexSet_partition (G : MultiGraph V E) :
    ∀ e : G.CrossEdge ({G.vertexSet} : Finset (Set V)), False := by
  classical
  intro e
  rcases e.2 with ⟨_heG, _x, _y, _hlink, U, hU, W, hW, hUW, _hxU, _hyW⟩
  have hUeq : U = G.vertexSet := by simpa using hU
  have hWeq : W = G.vertexSet := by simpa using hW
  exact hUW (hUeq.trans hWeq.symm)

lemma quotientEdgesCoveredByZero_single_vertexSet_partition (G : MultiGraph V E) :
    G.QuotientEdgesCoveredByKSpanningTrees ({G.vertexSet} : Finset (Set V)) 0 := by
  refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro e
    exact False.elim (no_crossEdge_single_vertexSet_partition G e)

/-- The `k = 0` specialization of Diestel, Theorem 2.4.4. -/
theorem theorem_2_4_4_k_zero {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.Loopless →
      G.Connected →
        ∃ P : Finset (Set V), G.PackingCoveringPartition P 0 := by
  intro _hloopless hconn
  classical
  haveI : Nonempty G.vertexSet := hconn.nonempty
  have hVne : G.vertexSet.Nonempty := by
    rcases (Classical.choice ‹Nonempty G.vertexSet›) with ⟨x, hx⟩
    exact ⟨x, hx⟩
  let P : Finset (Set V) := {G.vertexSet}
  refine ⟨P, ?_, ?_, ?_⟩
  · exact single_vertexSet_partition (G := G) hVne
  · intro U _hU
    exact hasZeroEdgeDisjointSpanningTreesOn G U
  · exact quotientEdgesCoveredByZero_single_vertexSet_partition G

end MultiGraph

end Chapter02
end Diestel
