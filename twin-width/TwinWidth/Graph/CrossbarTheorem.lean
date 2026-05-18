import TwinWidth.Graph.CrossbarContract
import TwinWidth.Graph.PathOfSetsGrid

/-!
# Crossbar dichotomy theorem

This module exposes the Chuzhoy--Tan crossbar dichotomy outside the contract
namespace.  The current proof is the corresponding contract axiom; the file is
the intended import point for the later proof of the polynomial grid-minor
theorem.
-/

namespace TwinWidth
namespace SimpleGraph

namespace CrossbarContract

/-- The strong-path-of-sets-minor outcome is monotone under adding edges to the
host graph. -/
theorem HasStrongPathOfSetsMinor.mono {V : Type u} [DecidableEq V]
    {G G' : _root_.SimpleGraph V} {ell w : ℕ}
    (h : HasStrongPathOfSetsMinor G ell w) (hGG' : G ≤ G') :
    HasStrongPathOfSetsMinor G' ell w := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, hsystem⟩
  exact ⟨W, hWfin, hWdec, H, hminor.mono hGG', hsystem⟩

/-- The strong-path-of-sets-minor outcome transfers forward through an
arbitrary graph-minor relation. -/
theorem HasStrongPathOfSetsMinor.of_minor {W V : Type u}
    [DecidableEq W] [DecidableEq V]
    {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V} {ell w : ℕ}
    (h : HasStrongPathOfSetsMinor H ell w) (hminor : IsMinor H G) :
    HasStrongPathOfSetsMinor G ell w := by
  rcases h with ⟨U, hUfin, hUdec, F, hFH, hsystem⟩
  exact ⟨U, hUfin, hUdec, F, hFH.trans hminor, hsystem⟩

/-- The strong-path-of-sets-minor outcome is invariant under relabeling the
host graph. -/
theorem HasStrongPathOfSetsMinor.of_iso {V V' : Type u}
    [DecidableEq V] [DecidableEq V']
    {G : _root_.SimpleGraph V} {G' : _root_.SimpleGraph V'} {ell w : ℕ}
    (e : G ≃g G') (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G' ell w := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, hsystem⟩
  exact ⟨W, hWfin, hWdec, H, hminor.of_iso_right e, hsystem⟩

/-- Thin only the length of the strong path-of-sets system carried by a minor. -/
theorem HasStrongPathOfSetsMinor.restrictLength {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w ell' : ℕ}
    (hell_pos : 0 < ell') (hell : ell' ≤ ell)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G ell' w := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, hWfin, hWdec, H, hminor,
    ⟨Hsys.restrictLength hell_pos hell⟩⟩

/-- Thin only the width of the strong path-of-sets system carried by a minor. -/
theorem HasStrongPathOfSetsMinor.restrictWidth {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w w' : ℕ}
    (hw_pos : 0 < w') (hw : w' ≤ w)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G ell w' := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, hWfin, hWdec, H, hminor,
    ⟨Hsys.restrictWidth hw_pos hw⟩⟩

/-- Simultaneously thin the length and width of the strong path-of-sets system
carried by a minor. -/
theorem HasStrongPathOfSetsMinor.restrict {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w ell' w' : ℕ}
    (hell_pos : 0 < ell') (hw_pos : 0 < w')
    (hell : ell' ≤ ell) (hw : w' ≤ w)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G ell' w' := by
  rcases h with ⟨W, hWfin, hWdec, H, hminor, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, hWfin, hWdec, H, hminor,
    ⟨Hsys.restrict hell_pos hw_pos hell hw⟩⟩

/-- Thin the strong path-of-sets system carried by a minor to an exact square
length and width. -/
theorem HasStrongPathOfSetsMinor.restrictSquare {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} {ell w g : ℕ}
    (hg : 2 ≤ g) (hell : g ^ 2 ≤ ell) (hw : g ^ 2 ≤ w)
    (h : HasStrongPathOfSetsMinor G ell w) :
    HasStrongPathOfSetsMinor G (g ^ 2) (g ^ 2) := by
  exact h.restrict
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) hg))
    hell hw

/-- The exact strong-path-of-sets-minor outcome gives a grid minor by the
path-of-sets-to-grid theorem. -/
theorem HasStrongPathOfSetsMinor.exists_gridMinor :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {g : ℕ},
          2 ≤ g →
            HasStrongPathOfSetsMinor G (g ^ 2) (g ^ 2) →
              ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases PathOfSetsGrid.exists_gridMinor_of_strong_pathOfSets_minor with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G g hg hminor
  rcases hminor with ⟨W, hWfin, hWdec, H, hHG, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact hgrid H G hg hHG Hsys

/-- The strong Path-of-Sets minor outcome contains a grid minor whenever its
length and width dominate the square of the requested path-of-sets parameter. -/
theorem HasStrongPathOfSetsMinor.exists_gridMinor_of_large :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                HasStrongPathOfSetsMinor G ell w →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases HasStrongPathOfSetsMinor.exists_gridMinor with ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g hg hell hw hminor
  exact hgrid hg (hminor.restrictSquare hg hell hw)

/-- The exact strong-path-of-sets-minor outcome gives a grid minor, using
Chekuri--Chuzhoy Corollary 3.2 as an explicit input. -/
theorem HasStrongPathOfSetsMinor.exists_gridMinor_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {g : ℕ},
          2 ≤ g →
            HasStrongPathOfSetsMinor G (g ^ 2) (g ^ 2) →
              ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases
    PathOfSetsGrid.exists_gridMinor_of_strong_pathOfSets_minor_of_corollary32Input
      hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G g hg hminor
  rcases hminor with ⟨W, hWfin, hWdec, H, hHG, ⟨Hsys⟩⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact hgrid H G hg hHG Hsys

/-- The strong Path-of-Sets minor outcome contains a grid minor whenever its
length and width dominate the square of the requested path-of-sets parameter,
using Chekuri--Chuzhoy Corollary 3.2 as an explicit input. -/
theorem HasStrongPathOfSetsMinor.exists_gridMinor_of_large_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u}) :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : _root_.SimpleGraph V} {ell w g : ℕ},
          2 ≤ g →
            g ^ 2 ≤ ell →
              g ^ 2 ≤ w →
                HasStrongPathOfSetsMinor G ell w →
                  ∃ g' : ℕ, g ≤ c * g' ∧ ContainsGridMinor G g' := by
  rcases HasStrongPathOfSetsMinor.exists_gridMinor_of_corollary32Input hinput with
    ⟨c, hc, hgrid⟩
  refine ⟨c, hc, ?_⟩
  intro V _ _ G ell w g hg hell hw hminor
  exact hgrid hg (hminor.restrictSquare hg hell hw)

end CrossbarContract

namespace CrossbarTheorem

/-- Chuzhoy--Tan crossbar dichotomy: from large terminal sets with the required
path packings, either a crossbar exists or a minor contains a large strong
Path-of-Sets System. -/
theorem crossbar_or_strong_pathOfSets_minor :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (H : _root_.SimpleGraph V) {g kappa : ℕ}
        {A B X : Finset V},
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              A.card = kappa →
                B.card = kappa →
                  X.card = kappa →
                    Disjoint A B →
                      Disjoint A X →
                        Disjoint B X →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ kappa →
                            (∀ x ∈ X, DegreeEquals H x 1) →
                              (Pab : PathPacking H A B) →
                                Pab.card = kappa →
                                  (Pax : PathPacking H A X) →
                                    Pax.card = kappa →
                                      Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                        ∃ ell w : ℕ,
                                          g ^ 2 ≤ c * ell ∧
                                            g ^ 2 ≤ c * w ∧
                                              CrossbarContract.HasStrongPathOfSetsMinor H ell w := by
  exact CrossbarContract.crossbar_or_strong_pathOfSets_minor

end CrossbarTheorem
end SimpleGraph
end TwinWidth
