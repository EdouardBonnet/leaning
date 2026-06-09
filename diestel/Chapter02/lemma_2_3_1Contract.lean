import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Lemma 2.3.1.
Natural-language statement:
For every `k`, every sufficiently large cubic multigraph contains `k`
disjoint cycles.
-/
axiom lemma_2_3_1 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.IsCubic G →
    erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
      MultiGraph.HasKDisjointCycles G k

end Chapter02
end Diestel
