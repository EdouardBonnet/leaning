import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma hasZeroDisjointCycles (G : MultiGraph V E) :
    G.HasKDisjointCycles 0 := by
  refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_⟩
  intro i _j _hij
  exact Fin.elim0 i

/-- The `k = 0` specialization of Diestel, Lemma 2.3.1. -/
theorem lemma_2_3_1_k_zero {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.IsCubic →
      erdosPosaS 0 < (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointCycles 0 := by
  intro _hCubic _hLarge
  exact hasZeroDisjointCycles G

end MultiGraph

end Chapter02
end Diestel
