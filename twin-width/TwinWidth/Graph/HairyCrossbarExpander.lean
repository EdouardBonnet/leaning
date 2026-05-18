import TwinWidth.Graph.HairyCrossbar
import TwinWidth.Graph.HairyCrossbarGridExpander

/-!
# Hairy crossbar wrappers using the explicit expander theorem handoff

This module lifts the `HairyCrossbarGridExpander` handoff through the local
crossbar dichotomy.  It is the Chuzhoy--Tan proof-facing interface after
Theorem 8.1 has been internalized: the remaining large-case inputs are a
fixed-round cut-matching transcript provider and the explicit target-size
arithmetic for Theorem 8.1.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyPathOfSetsSystem

universe u

/-- Hairy path-of-sets dichotomy using the explicit Theorem 8.1 target-size
provider in the direct grid-minor branch. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_transcript_and_targetProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingTranscriptProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor with
    ⟨cCross, hcCross, hodd⟩
  rcases
    _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_transcript_and_target
      hproviders with
    ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cCross, cGrid, hcCross, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hmaxDegree hell hw hlarge
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hmaxDegree hell hw hcrossbars)
  · exact Or.inr hstrong

/-- Hairy path-of-sets dichotomy using an unbundled cut-matching sequence
provider and the explicit Theorem 8.1 target-size provider. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_unbundledCutMatching_and_targetProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' :=
  gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_transcript_and_targetProviders
    (by
      rcases hproviders with
        ⟨cRound, cScale, hcRound, hcScale, hunbundled, htarget⟩
      exact ⟨cRound, cScale, hcRound, hcScale,
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundCutMatchingTranscriptProvider_of_unbundled
          hunbundled,
        htarget⟩)

/-- Hairy path-of-sets dichotomy after internalizing the Theorem 8.1
target-size arithmetic.  The only remaining large-case input is the
fixed-round unbundled cut-matching provider. -/
theorem gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_unbundledCutMatching
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid : ℕ, 0 < cCross ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (_ : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                cGrid * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                      (∃ g' : ℕ,
                        g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g') ∨
                        ∃ ell' w' : ℕ,
                          g ^ 2 ≤ cCross * ell' ∧
                            g ^ 2 ≤ cCross * w' ∧
                              CrossbarContract.HasStrongPathOfSetsMinor
                                G ell' w' := by
  rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
  exact
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_unbundledCutMatching_and_targetProviders
      ⟨cRound,
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
          cRound,
        hcRound,
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
          cRound,
        hunbundled,
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
          cRound⟩

/-- Scaled-strong-parameter version using the unbundled fixed-round
cut-matching provider and the explicit Theorem 8.1 target-size provider for
the direct crossbar-grid branch. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_unbundledCutMatching_and_targetProviders
      hproviders with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases CrossbarContract.HasStrongPathOfSetsMinor.exists_gridMinor_of_large with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le hcCross hscaled hell')
      (square_le_of_scaled_square_le hcCross hscaled hw')
      hminor)

/-- Scaled-strong-parameter version using the unbundled fixed-round
cut-matching provider and the explicit Theorem 8.1 target-size provider, with
the strong-minor-to-grid branch supplied by Chekuri--Chuzhoy Corollary 3.2 as
an explicit input. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' := by
  rcases
    gridMinor_or_strong_pathOfSets_minor_of_hairy_pathOfSets_of_unbundledCutMatching_and_targetProviders
      hproviders with
    ⟨cCross, cGrid, hcCross, hcGrid, hmain⟩
  rcases
    CrossbarContract.HasStrongPathOfSetsMinor.exists_gridMinor_of_large_of_corollary32Input
      hinput with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain G Hsys hg hpow hmaxDegree hell hw hlarge with
    hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le hcCross hscaled hell')
      (square_le_of_scaled_square_le hcCross hscaled hw')
      hminor)

/-- Corollary-3.2-input version after internalizing the Theorem 8.1 target-size
arithmetic. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u})
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
    hinput
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact
        ⟨cRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
            cRound,
          hcRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
            cRound,
          hunbundled,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
            cRound⟩)

/-- Local-routing/stitching version of the scaled-strong-parameter handoff with
the explicit Theorem 8.1 target-size provider. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_localRouting_and_stitching
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hproviders

/-- Local-routing/stitching version after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_of_localRouting_and_stitching
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hprovider

/-- Scaled-strong-parameter version after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem G ell w),
            2 ≤ g →
              2 ≤ r →
                CrossbarContract.IsPowerOfTwo g →
                  MaxDegreeAtMost G 3 →
                    cGrid * Nat.log 2 g ≤ ell →
                      g ^ 2 ≤ w →
                        2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                          cCross * r ^ 2 ≤ g ^ 2 →
                            (∃ g' : ℕ,
                              g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                ContainsGridMinor G g') ∨
                              ∃ r' : ℕ,
                                r ≤ cStrong * r' ∧
                                  ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact
        ⟨cRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
            cRound,
          hcRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
            cRound,
          hunbundled,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
            cRound⟩)

/-- Supergraph version of
`gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders`. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases
    gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders
      hproviders with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Supergraph version with the strong-minor branch supplied by
Chekuri--Chuzhoy Corollary 3.2 as an explicit input. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases
    gridMinor_or_gridMinor_of_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
      hinput hproviders with
    ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, hmain⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hmain H Hsys hg hr hpow hmaxDegree hell hw hlarge hscaled with
    hgrid | hgrid
  · rcases hgrid with ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hgrid with ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Supergraph Corollary-3.2-input version after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_of_corollary32Input
    (hinput : ChekuriChuzhoy.Corollary32Input.{u})
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
    hinput
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact
        ⟨cRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
            cRound,
          hcRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
            cRound,
          hunbundled,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
            cRound⟩)

/-- Supergraph local-routing/stitching version with the explicit Theorem 8.1
target-size provider. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_localRouting_and_stitching
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hproviders

/-- Supergraph local-routing/stitching version after internalizing the Theorem
8.1 target-size arithmetic. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_of_localRouting_and_stitching
    (hlocal : ChekuriChuzhoy.LocalRoutingInput.{u})
    (hstitch : ChekuriChuzhoy.StitchingInput.{u})
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_of_corollary32Input
    (ChekuriChuzhoy.corollary32Input_of_localRoutingInput_and_stitchingInput
      hlocal hstitch)
    hprovider

/-- Explicit-input supergraph version of the target-provider route.  The
crossbar dichotomy, the strong-minor-to-grid theorem, and the unbundled
cut-matching/target-size package are all supplied as hypotheses. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hproviders :
      ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound ∧
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundExpanderTargetProvider
            cRound cScale) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' := by
  rcases local_crossbars_at_odd_clusters_or_strong_pathOfSets_minor_of_crossbarDichotomy
      hcrossInput with
    ⟨cCross, hcCross, hodd⟩
  rcases
    _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_unbundled_and_target
      hproviders with
    ⟨cGrid, hcGrid, hgrid⟩
  rcases hstrongGrid with ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cCross, cGrid, cStrong, hcCross, hcGrid, hcStrong, ?_⟩
  intro V _ _ G H ell w g r Hsys hHG hg hr hpow hmaxDegree hell hw hlarge
    hscaled
  rcases hodd Hsys hg hpow hlarge with hcrossbars | hstrong
  · rcases hgrid H Hsys hg hpow hmaxDegree hell hw hcrossbars with
      ⟨g', hbound, hgrid⟩
    exact Or.inl ⟨g', hbound, hgrid.mono hHG⟩
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    rcases hstrongGrid hr
        (square_le_of_scaled_square_le hcCross hscaled hell')
        (square_le_of_scaled_square_le hcCross hscaled hw')
        hminor with
      ⟨r', hbound, hgrid⟩
    exact Or.inr ⟨r', hbound, hgrid.mono hHG⟩

/-- Explicit-input supergraph version after internalizing the Theorem 8.1
target-size arithmetic. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching
    (hcrossInput : ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInput.{u} c)
    (hstrongGrid :
      ∃ cStrong : ℕ, 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          {G : _root_.SimpleGraph V} {ell w g : ℕ},
            2 ≤ g →
              g ^ 2 ≤ ell →
                g ^ 2 ≤ w →
                  CrossbarContract.HasStrongPathOfSetsMinor G ell w →
                    ∃ g' : ℕ, g ≤ cStrong * g' ∧ ContainsGridMinor G g')
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_inputs_and_unbundledCutMatching_and_targetProviders
    hcrossInput hstrongGrid
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact
        ⟨cRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
            cRound,
          hcRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
            cRound,
          hunbundled,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
            cRound⟩)

/-- Supergraph version after internalizing the Theorem 8.1 target-size
arithmetic. -/
theorem gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching
    (hprovider :
      ∃ cRound : ℕ, 0 < cRound ∧
        _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.FixedRoundCutMatchingUnbundledProvider.{u}
          cRound) :
    ∃ cCross cGrid cStrong : ℕ,
      0 < cCross ∧ 0 < cGrid ∧ 0 < cStrong ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G H : _root_.SimpleGraph V) {ell w g r : ℕ}
          (_ : HairyPathOfSetsSystem H ell w),
            H ≤ G →
              2 ≤ g →
                2 ≤ r →
                  CrossbarContract.IsPowerOfTwo g →
                    MaxDegreeAtMost H 3 →
                      cGrid * Nat.log 2 g ≤ ell →
                        g ^ 2 ≤ w →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ w →
                            cCross * r ^ 2 ≤ g ^ 2 →
                              (∃ g' : ℕ,
                                g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
                                  ContainsGridMinor G g') ∨
                                ∃ r' : ℕ,
                                  r ≤ cStrong * r' ∧
                                    ContainsGridMinor G r' :=
  gridMinor_or_gridMinor_of_subgraph_hairy_pathOfSets_with_scaled_strong_parameter_of_unbundledCutMatching_and_targetProviders
    (by
      rcases hprovider with ⟨cRound, hcRound, hunbundled⟩
      exact
        ⟨cRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale
            cRound,
          hcRound,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetScale_pos
            cRound,
          hunbundled,
          _root_.TwinWidth.SimpleGraph.HairyCrossbarGrid.fixedRoundExpanderTargetProvider_explicit
            cRound⟩)

end HairyPathOfSetsSystem
end SimpleGraph
end TwinWidth
