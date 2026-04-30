import TwinWidth.Matrix.Cell

/-!
# Mixed minors of Boolean matrices

This file defines `HasMixedMinor`.  The `k = 0` convention is intentionally
vacuous: every matrix has a `0`-mixed minor, witnessed by the empty family of
cells.  Positive mixed minors require concrete row and column divisions.
-/

namespace TwinWidth
namespace Matrix

/-- A Boolean matrix has a `k`-mixed minor if it admits row and column
`k`-divisions whose every cell is mixed. -/
def HasMixedMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ R : Division n k, ∃ C : Division m k,
      ∀ i j : Fin k, CellMixed M R C i j

@[simp] theorem hasMixedMinor_zero {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool) : HasMixedMinor M 0 :=
  Or.inl rfl

end Matrix
end TwinWidth
