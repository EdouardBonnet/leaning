import TwinWidth.Graph.CutMatchingGameContract
import TwinWidth.Graph.HairyCrossbarGridExpander

/-!
# Cut-matching game bridge

This file packages the Section 4 cut-matching-game theorem in the provider
form consumed by the large crossbar-grid assembly.

The current proof is intentionally a narrow bridge from the contract statement
in `CutMatchingGameContract` to the repository's existing
`FixedRoundCutMatchingUnbundledProvider` interface.  Once the entropy-potential
proof from Section 4 is formalized, this file is the place where the contract
import should be replaced by the self-contained proof.
-/

namespace TwinWidth
namespace SimpleGraph
namespace HairyCrossbarGrid

universe u

/-- The cut-matching-game upper bound supplies the unbundled fixed-round
provider used by the crossbar-grid construction: after `O(log g)` rounds,
the transported matching union is a half-edge-expander. -/
theorem exists_fixedRoundCutMatchingUnbundledProvider :
    ∃ cRound : ℕ, 0 < cRound ∧
      FixedRoundCutMatchingUnbundledProvider.{u} cRound := by
  rcases
    CutMatchingGameContract.exists_bisection_strategy_transported_matchings_half_expander
    with ⟨cRound, hcRound, hstrategy⟩
  refine ⟨cRound, hcRound, ?_⟩
  intro V _ _ G ell w g Hsys hg hpow hdeg hrounds hw hcrossbars
  exact hstrategy G Hsys hg hpow hdeg hrounds hw hcrossbars

/-- Combining the cut-matching-game upper bound with the already formalized
explicit Theorem 8.1 target-size arithmetic gives the fixed-round expander
data provider used by the crossbar-grid assembly. -/
theorem exists_fixedRoundLargeCaseExpanderDataProvider_of_cutMatchingGame :
    ∃ cRound cScale : ℕ, 0 < cRound ∧ 0 < cScale ∧
      FixedRoundLargeCaseExpanderDataProvider.{u} cRound cScale := by
  rcases exists_fixedRoundCutMatchingUnbundledProvider.{u} with
    ⟨cRound, hcRound, hcutMatching⟩
  exact exists_fixedRoundLargeCaseExpanderDataProvider_of_unbundled_and_target
    ⟨cRound, fixedRoundExpanderTargetScale cRound,
      hcRound, fixedRoundExpanderTargetScale_pos cRound,
      hcutMatching, fixedRoundExpanderTargetProvider_explicit cRound⟩

/-- Crossbar-grid assembly with the large case supplied by the
cut-matching-game theorem rather than by the old large-case contract. -/
theorem exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              MaxDegreeAtMost G 3 →
                c * Nat.log 2 g ≤ ell →
                  g ^ 2 ≤ w →
                    (∀ i : Fin ell, OneBasedOdd i →
                      Nonempty (Crossbar (Hsys.hairLocalGraph i)
                        (Hsys.base.left i) (Hsys.base.right i)
                        (Hsys.y i) (g ^ 2))) →
                      ∃ g' : ℕ,
                        g ≤ c * g' * (Nat.log 2 g) ^ 2 ∧
                          ContainsGridMinor G g' :=
  exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_fixedRoundExpanderDataProvider
    exists_fixedRoundLargeCaseExpanderDataProvider_of_cutMatchingGame

end HairyCrossbarGrid
end SimpleGraph
end TwinWidth
