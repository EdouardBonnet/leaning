import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.5.1 (Gallai-Milgram).
Natural-language statement:
Every finite directed graph has a path cover with one representative
vertex from each path, and the representatives form an independent set.
-/
axiom theorem_2_5_1 {V : Type u} [Fintype V] [DecidableEq V]
    (D : DirectedGraph V) :
  HasIndependentPathCoverRepresentatives D

end Chapter02
end Diestel
