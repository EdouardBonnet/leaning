import Mathlib.Data.Matrix.Basic
import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.IntervalDivision

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Matrix
namespace Cell

variable {α : Type*}

/-- A divided matrix cell is vertical when each of its columns is constant
inside the row part. -/
def Vertical {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : IntervalDivision.Division n k) (C : IntervalDivision.Division m k)
    (i j : Fin k) : Prop :=
  ∀ ⦃r₁ r₂ : Fin n⦄,
    r₁ ∈ IntervalDivision.part R i → r₂ ∈ IntervalDivision.part R i →
    ∀ ⦃c : Fin m⦄, c ∈ IntervalDivision.part C j → M r₁ c = M r₂ c

/-- A divided matrix cell is horizontal when each of its rows is constant
inside the column part. -/
def Horizontal {n m k : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α)
    (R : IntervalDivision.Division n k) (C : IntervalDivision.Division m k)
    (i j : Fin k) : Prop :=
  ∀ ⦃r : Fin n⦄, r ∈ IntervalDivision.part R i →
    ∀ ⦃c₁ c₂ : Fin m⦄,
      c₁ ∈ IntervalDivision.part C j → c₂ ∈ IntervalDivision.part C j →
      M r c₁ = M r c₂

end Cell
end Matrix
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
