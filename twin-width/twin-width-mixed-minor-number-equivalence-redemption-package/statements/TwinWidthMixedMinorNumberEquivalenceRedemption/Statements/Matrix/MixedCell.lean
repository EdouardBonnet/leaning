import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.Cell

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Matrix
namespace MixedCell

variable {α : Type*}

/-- A divided matrix cell is mixed when it is neither vertical nor horizontal. -/
def Mixed {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : IntervalDivision.Division n k) (C : IntervalDivision.Division m k)
    (i j : Fin k) : Prop :=
  ¬ Cell.Vertical M R C i j ∧ ¬ Cell.Horizontal M R C i j

end MixedCell
end Matrix
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
