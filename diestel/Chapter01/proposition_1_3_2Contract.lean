import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.3.2.
Natural-language statement:
Every graph containing a cycle satisfies `g(G) ≤ 2 * diam(G) + 1`.

Lean convention note:
Mathlib's finite `diam` is `0` for disconnected graphs, whereas Diestel's
distance convention makes the relevant diameter infinite outside connected
graphs. The finite `diam` version therefore carries connectedness explicitly.
-/
axiom proposition_1_3_2 {V : Type u} (G : SimpleGraph V) [Finite V] [Nonempty V] :
  G.Connected → ¬ G.IsAcyclic → G.girth ≤ 2 * G.diam + 1

end Chapter01
end Diestel
