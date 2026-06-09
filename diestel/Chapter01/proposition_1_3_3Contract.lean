import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Diam

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.3.3.
Natural-language statement:
A graph of radius at most `k` and maximum degree at most `d ≥ 3` has
fewer than `d / (d - 2) * (d - 1)^k` vertices.
-/
axiom proposition_1_3_3 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [Nonempty V] [DecidableRel G.Adj] (k d : ℕ) :
  G.radius ≤ (k : ℕ∞) →
    G.maxDegree ≤ d →
      3 ≤ d →
        (Fintype.card V : ℚ) <
          ((d : ℚ) / ((d : ℚ) - 2)) * ((d : ℚ) - 1) ^ k

end Chapter01
end Diestel
