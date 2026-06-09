import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Copy

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

/--
Diestel, Corollary 1.5.3.
Natural-language statement:
If `T` is a tree and `δ(G) > |T| - 1`, then `G` contains a copy of `T`.
-/
axiom corollary_1_5_3 {V : Type u} {W : Type v}
    (T : SimpleGraph W) (G : SimpleGraph V)
    [Fintype W] [Fintype V] [DecidableRel G.Adj] :
  T.IsTree → Fintype.card W - 1 < G.minDegree → SimpleGraph.IsContained T G

end Chapter01
end Diestel
