import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.8.1 (Euler).
Natural-language statement:
A connected graph is Eulerian iff every vertex has even degree.
-/
axiom theorem_1_8_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
  G.Connected → (IsEulerian G ↔ ∀ v : V, Even (G.degree v))

end Chapter01
end Diestel
