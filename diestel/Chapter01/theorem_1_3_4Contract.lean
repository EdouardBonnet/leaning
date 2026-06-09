import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Girth

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.3.4 (Alon-Hoory-Linial).
Natural-language statement:
If `d(G) ≥ d ≥ 2` and `g(G) ≥ g`, then `|G| ≥ n₀(d,g)`.
-/
axiom theorem_1_3_4 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (d : ℝ) (g : ℕ) :
  2 ≤ d →
    d ≤ (average_degree G : ℝ) →
      (g : ℕ∞) ≤ G.egirth →
        n0 d g ≤ (Fintype.card V : ℝ)

end Chapter01
end Diestel
