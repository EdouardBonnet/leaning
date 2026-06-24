import TwinWidth.Matrix.Cell









namespace TwinWidth
namespace Matrix

variable {α : Type*}



def HasMixedMinor {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) α) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ R : Division n k, ∃ C : Division m k,
      ∀ i j : Fin k, CellMixed M R C i j

@[simp] theorem hasMixedMinor_zero {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) α) : HasMixedMinor M 0 :=
  Or.inl rfl


theorem hasMixedMinor_le_min_card {n m k : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) α}
    (h : HasMixedMinor M k) : k ≤ min n m := by
  rcases h with rfl | h
  · exact Nat.zero_le _
  · rcases h with ⟨R, C, _⟩
    exact le_min (Division.card_parts_le R) (Division.card_parts_le C)

end Matrix
end TwinWidth
