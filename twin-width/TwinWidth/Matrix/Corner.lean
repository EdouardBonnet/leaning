import TwinWidth.Matrix.MixedValue

/-!
# Corners

This file proves the rectangular core of Lemma 11 from Section 5: a Boolean
zone is mixed exactly when it contains a mixed `2 × 2` submatrix.  The paper
then localizes such a submatrix to adjacent rows and columns inside consecutive
intervals; that localization is kept separate from this algebraic statement.
-/

namespace TwinWidth
namespace Matrix

/-- A mixed `2 × 2` submatrix inside a rectangular zone. -/
def ZoneCorner {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (R : Finset (Fin n)) (C : Finset (Fin m)) : Prop :=
  ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C,
    ((M r₁ c₁ ≠ M r₂ c₁) ∨ (M r₁ c₂ ≠ M r₂ c₂)) ∧
      ((M r₁ c₁ ≠ M r₁ c₂) ∨ (M r₂ c₁ ≠ M r₂ c₂))

theorem not_zoneVertical_iff_exists {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneVertical M R C ↔
      ∃ r₁ ∈ R, ∃ r₂ ∈ R, ∃ c ∈ C, M r₁ c ≠ M r₂ c := by
  classical
  simp [ZoneVertical]

theorem not_zoneHorizontal_iff_exists {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ¬ ZoneHorizontal M R C ↔
      ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, M r c₁ ≠ M r c₂ := by
  classical
  simp [ZoneHorizontal]

theorem zoneCorner_of_zoneMixed {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) Bool}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneMixed M R C) : ZoneCorner M R C := by
  classical
  rcases (not_zoneVertical_iff_exists M R C).mp h.1 with
    ⟨a, ha, b, hb, x, hx, habx⟩
  rcases (not_zoneHorizontal_iff_exists M R C).mp h.2 with
    ⟨r, hr, y, hy, z, hz, hryz⟩
  by_cases hay : M a x ≠ M a y
  · exact ⟨a, ha, b, hb, x, hx, y, hy, Or.inl habx, Or.inl hay⟩
  · have hay' : M a x = M a y := Classical.not_not.mp hay
    by_cases hby : M b x ≠ M b y
    · exact ⟨a, ha, b, hb, x, hx, y, hy, Or.inl habx, Or.inr hby⟩
    · have hby' : M b x = M b y := Classical.not_not.mp hby
      by_cases haz : M a x ≠ M a z
      · exact ⟨a, ha, b, hb, x, hx, z, hz, Or.inl habx, Or.inl haz⟩
      · have haz' : M a x = M a z := Classical.not_not.mp haz
        by_cases hbz : M b x ≠ M b z
        · exact ⟨a, ha, b, hb, x, hx, z, hz, Or.inl habx, Or.inr hbz⟩
        · have hbz' : M b x = M b z := Classical.not_not.mp hbz
          have hayz : M a y = M a z := hay'.symm.trans haz'
          by_cases hrya : M r y ≠ M a y
          · exact ⟨r, hr, a, ha, y, hy, z, hz, Or.inl hrya, Or.inl hryz⟩
          · have hrya' : M r y = M a y := Classical.not_not.mp hrya
            have hrza : M r z ≠ M a z := by
              intro hrza
              exact hryz (hrya'.trans (hayz.trans hrza.symm))
            exact ⟨r, hr, a, ha, y, hy, z, hz, Or.inr hrza, Or.inl hryz⟩

theorem zoneMixed_of_zoneCorner {n m : ℕ}
    {M : _root_.Matrix (Fin n) (Fin m) Bool}
    {R : Finset (Fin n)} {C : Finset (Fin m)}
    (h : ZoneCorner M R C) : ZoneMixed M R C := by
  rcases h with ⟨r₁, hr₁, r₂, hr₂, c₁, hc₁, c₂, hc₂, hvert, hhoriz⟩
  constructor
  · intro hv
    rcases hvert with h | h
    · exact h (hv hr₁ hr₂ hc₁)
    · exact h (hv hr₁ hr₂ hc₂)
  · intro hh
    rcases hhoriz with h | h
    · exact h (hh hr₁ hc₁ hc₂)
    · exact h (hh hr₂ hc₁ hc₂)

/-- A rectangular Boolean zone is mixed iff it contains a mixed `2 × 2`
submatrix. -/
theorem zoneMixed_iff_zoneCorner {n m : ℕ}
    (M : _root_.Matrix (Fin n) (Fin m) Bool)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    ZoneMixed M R C ↔ ZoneCorner M R C :=
  ⟨zoneCorner_of_zoneMixed, zoneMixed_of_zoneCorner⟩

end Matrix
end TwinWidth
