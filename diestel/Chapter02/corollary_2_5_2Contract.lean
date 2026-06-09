import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Corollary 2.5.2 (Dilworth).
Natural-language statement:
In every finite partially ordered set, the minimum number of chains needed
to cover the set is equal to the maximum size of an antichain.
-/
axiom corollary_2_5_2 (P : Type u) [Fintype P] [DecidableEq P] [PartialOrder P] :
  ChainCover P (maxAntichainCard P) ∧
    ∀ n : ℕ, ChainCover P n → maxAntichainCard P ≤ n

end Chapter02
end Diestel
