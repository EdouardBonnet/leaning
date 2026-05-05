import TwinWidth.Matrix.DivisionSequence

/-!
# Contract statement for Lemma 13 division sequences

This file states the final readable mathematical interface of the
Marcus--Tardos-to-division-sequence argument.
-/

namespace TwinWidth
namespace Matrix
namespace DivisionSequenceContract

variable {α : Type*}

/-- Lemma 13, sequence form: a positive-size `t`-mixed-free matrix has a full
division sequence from the finest division to the coarsest division whose mixed
value is always at most `20 * c t`. -/
theorem lemma13_bounded_mixed_value_division_sequence
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (M : _root_.Matrix (Fin n) (Fin m) α) (t : ℕ),
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (20 * c t)) := by
  exact TwinWidth.Matrix.lemma13_bounded_mixed_value_division_sequence hMT

end DivisionSequenceContract
end Matrix
end TwinWidth
