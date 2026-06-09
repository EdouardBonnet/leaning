import Chapter02.cycle_packing_k_zero_aux
import Chapter02.cycle_packing_k_one_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

/--
The `k ≤ 1` part of Diestel, Lemma 2.3.1.  The case `k = 0` is empty,
and the case `k = 1` follows from the compiled cycle-existence argument in
`cycle_packing_k_one_aux`.
-/
theorem lemma_2_3_1_small_k {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
    k ≤ 1 →
      G.IsCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointCycles k := by
  intro hk hCubic hLarge
  interval_cases k
  · exact lemma_2_3_1_k_zero G hCubic hLarge
  · exact lemma_2_3_1_k_one G hCubic hLarge

end MultiGraph

end Chapter02
end Diestel
