import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.9.7.
Natural-language statement:
For the real incidence matrix `B`, adjacency matrix `A`, and degree
diagonal matrix `D`, one has `B * Bᵀ = A + D`.
-/
axiom proposition_1_9_7 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
  G.incMatrix ℝ * Matrix.transpose (G.incMatrix ℝ) =
    G.adjMatrix ℝ + Matrix.diagonal (fun v : V => (G.degree v : ℝ))

end Chapter01
end Diestel
