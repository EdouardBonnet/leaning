import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.3.2 (Erdos-Posa).
Natural-language statement:
There is a function `f : ℕ → ℕ` such that every finite graph contains
either `k` disjoint cycles or a set of at most `f k` vertices meeting all
cycles.
-/
axiom theorem_2_3_2 :
  ∃ f : ℕ → ℕ, ErdosPosaCycleBound f

end Chapter02
end Diestel
