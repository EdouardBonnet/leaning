import TwinWidth.Matrix.DivisionSequence

/-!
# Contract statements for Lemma 13 division sequences

This contract file states only the final readable mathematical interface of the
Marcus--Tardos-to-division-sequence argument.  The full proof file
`DivisionSequence.lean` proves this statement independently.
-/

namespace TwinWidth
namespace Matrix
namespace DivisionSequenceContract

/-- Lemma 13, sequence form: a positive-size `t`-mixed-free matrix has a full
division sequence from the finest division to the coarsest division whose mixed
value is always at most `20 * c t`. -/
axiom lemma13_bounded_mixed_value_division_sequence
    {c : ℕ → ℕ}
    (hMT : ∀ t : ℕ, IsMarcusTardosConstant t (c t)) :
    ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (M : _root_.Matrix (Fin n) (Fin m) Bool) (t : ℕ),
        MixedFree M t →
          Nonempty (BoundedMixedValueDivisionSequence M (20 * c t))

end DivisionSequenceContract
end Matrix
end TwinWidth
