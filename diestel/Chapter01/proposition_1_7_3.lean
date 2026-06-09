import Chapter01.topological_to_minor
import Chapter01.minor_to_topological

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

/--
Diestel, Proposition 1.7.3.
Topological minors are minors. Conversely, every minor whose source has
maximum degree at most `3` is a topological minor.
-/
theorem proposition_1_7_3 {V : Type u} {W : Type v}
    (X : SimpleGraph W) (G : SimpleGraph V)
    [Fintype W] [DecidableRel X.Adj] :
    (IsTopologicalMinor X G → IsMinor X G) ∧
      (X.maxDegree ≤ 3 → IsMinor X G → IsTopologicalMinor X G) := by
  constructor
  · exact isMinor_of_isTopologicalMinor X G
  · exact isTopologicalMinor_of_isMinor_of_maxDegree_le_three X G

end Chapter01
end Diestel
