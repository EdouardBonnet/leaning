import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedCell

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Matrix
namespace MixedMinor

variable {α : Type*}

/-- A matrix has a k-mixed minor if either k = 0, or it admits row and
column k-divisions whose every cell is mixed. -/
def HasMixedMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (k : ℕ) :
    Prop :=
  k = 0 ∨
    ∃ R : IntervalDivision.Division n k,
      ∃ C : IntervalDivision.Division m k,
        ∀ i j : Fin k, MixedCell.Mixed M R C i j

end MixedMinor
end Matrix
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
