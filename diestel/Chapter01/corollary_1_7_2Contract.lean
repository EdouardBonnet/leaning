import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

/--
Diestel, Corollary 1.7.2.
Natural-language statement:
For finite graphs, `X` is a minor of `Y` iff `X` can be obtained from `Y`
by a finite sequence of edge deletions, edge contractions, and vertex
deletions.

Contract note:
The current definition surface represents the right-hand side by the
existence of a finite minor model. A concrete contraction-step relation
should be selected before proving this contract.
-/
axiom corollary_1_7_2 {V : Type u} {W : Type v}
    (X : SimpleGraph W) (Y : SimpleGraph V) :
  Finite V → Finite W → (IsMinor X Y ↔ ∃ M : Model X Y, ∀ x : W, (M.branchSet x).Finite)

end Chapter01
end Diestel
