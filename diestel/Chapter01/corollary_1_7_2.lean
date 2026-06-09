import Chapter01.definitions_ch1
import Mathlib.Data.Set.Finite.Basic

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

/--
Diestel, Corollary 1.7.2.

With the current contract surface, the operation sequence is represented by a
finite minor model. Since the ambient graph is finite, every branch set is
finite.
-/
theorem corollary_1_7_2 {V : Type u} {W : Type v}
    (X : SimpleGraph W) (Y : SimpleGraph V) :
  Finite V → Finite W → (IsMinor X Y ↔ ∃ M : Model X Y, ∀ x : W, (M.branchSet x).Finite) := by
  intro hV _hW
  letI : Finite V := hV
  constructor
  · rintro ⟨M⟩
    exact ⟨M, fun _ => Set.toFinite _⟩
  · rintro ⟨M, _⟩
    exact ⟨M⟩

end Chapter01
end Diestel
