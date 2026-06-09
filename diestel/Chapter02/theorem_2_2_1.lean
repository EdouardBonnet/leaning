import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.2.1 (Tutte).
Natural-language statement:
A finite graph has a 1-factor if and only if it satisfies Tutte's
condition.
-/
theorem theorem_2_2_1 {V : Type u} (G : SimpleGraph V) [Finite V] :
  (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ TutteCondition G := by
  simpa [TutteCondition] using (SimpleGraph.tutte (G := G))

end Chapter02
end Diestel
