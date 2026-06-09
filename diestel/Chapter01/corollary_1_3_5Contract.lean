import Chapter01.definitions_ch1
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Girth

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Corollary 1.3.5.
Natural-language statement:
If `δ(G) ≥ 3`, then `g(G) < 2 log |G|`, where Diestel's `log` has base 2.
-/
axiom corollary_1_3_5 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  3 ≤ G.minDegree →
    (G.girth : ℝ) < 2 * (Real.log (Fintype.card V) / Real.log 2)

end Chapter01
end Diestel
