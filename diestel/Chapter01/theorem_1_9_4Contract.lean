import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.9.4.
Natural-language statement:
The cycle space and cut space are orthogonal complements:
`C = Bᗮ` and `B = Cᗮ`.
-/
axiom theorem_1_9_4 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
  ((cycle_space G : Set (EdgeSpace G)) = edge_orthogonal G (cut_space G)) ∧
    ((cut_space G : Set (EdgeSpace G)) = edge_orthogonal G (cycle_space G))

end Chapter01
end Diestel
