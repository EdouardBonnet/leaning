import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedMinor

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Matrix
namespace MixedNumber

variable {α : Type*}

/-- The mixed number of a matrix is the largest mixed-minor order searched up
to the smaller matrix dimension. -/
noncomputable def matrixMixedNumber {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) : ℕ :=
  sSup { k : ℕ | k ≤ min n m ∧ MixedMinor.HasMixedMinor M k }

end MixedNumber
end Matrix
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
