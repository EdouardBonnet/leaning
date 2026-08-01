import «statements-and-proofs».Exponent7.CutResponder.CutResponderNumericalEndpoint
import «statements-and-proofs».Exponent7.CutResponder.CutResponderGlobalDichotomyV2
import «statements-and-proofs».Exponent7.CutResponder.RoutingDescentV2

/-!
# Numerical endpoint for the existential clean active responder

The V2 responder changes only the routing quantifier.  The rounded scales,
all finite inequalities, and hence the exact degree-six threshold are reused
unchanged from `CutResponderNumericalEndpoint`.
-/

namespace SimpleGraph
namespace Exponent7
namespace CutResponder

universe u

/-- Consume a bundled numerical choice with the existential-routing graph
theorem. -/
theorem containsGridMinor_of_cleanResponderParameterChoiceV2
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    ∃ cRound cHair cHairLog cGrid : ℕ,
      0 < cRound ∧ 0 < cHair ∧
      0 < cHairLog ∧ 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) (target : ℕ),
          CleanResponderParameterChoice
              cHair cHairLog cGrid cRound
              responseConstant reserve target
              (treewidth G) →
            ContainsGridMinor G target := by
  rcases
      CutMatchingGame.exists_gridVertex_fixedRound_exact_list_halfExpander
      with ⟨cRound, hcRound, hstrategy⟩
  rcases
      containsGridMinor_of_treewidth_parameters_cleanActiveV2
        (cRound := cRound)
        (responseConstant := responseConstant)
        (reserve := reserve)
        hstrategy
        hclean
      with
    ⟨cHair, cHairLog, cGrid,
      hcHair, hcHairLog, hcGrid, hmain⟩
  refine
    ⟨cRound, cHair, cHairLog, cGrid,
      hcRound, hcHair, hcHairLog, hcGrid, ?_⟩
  intro V _ _ G target P
  exact
    hmain G P.ell_gt_one P.w_gt_one P.k_gt_one
      P.k_le_treewidth P.hairy_large
      P.cRound_pos P.responseConstant_pos P.reserve_pos
      P.pseudo_ge_two P.pseudo_powerOfTwo
      P.coordinate_ge_two P.coordinate_powerOfTwo
      P.target_le_coordinate
      P.systemLength_pos P.cut_length P.matching_width
      P.target_budget P.grid_length P.grid_width
      P.local_width P.target_outer

/-- Conditional excluded-grid theorem with exact polynomial power six under
the corrected routing-existential responder. -/
theorem polynomial_grid_minor_theorem_cleanResponderV2
    {reserve responseConstant : ℕ}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          polynomialGridMinorTreewidthBoundCleanResponder
              K b target ≤ treewidth G →
          ContainsGridMinor G target := by
  rcases
      containsGridMinor_of_cleanResponderParameterChoiceV2
        hclean hc hreserve
      with
    ⟨cRound, cHair, cHairLog, cGrid,
      hcRound, hcHair, hcHairLog, hcGrid, hmain⟩
  let T :=
    CleanResponderPolynomialTemplate.canonical
      cHair cHairLog cGrid cRound
      responseConstant reserve
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  let P :=
    T.toParameterChoice target htarget
      hcRound hc hreserve
  exact
    hmain G target
      { P with
        k_le_treewidth :=
          le_trans P.k_le_treewidth htw }

/-- The explicit rerouting-or-grid lemma is sufficient for the complete
degree-six conditional endpoint.  This theorem is the precise current
research boundary: `himprove` is an ordinary hypothesis, not an axiom. -/
theorem polynomial_grid_minor_theorem_of_routingImprovement
    {reserve responseConstant : ℕ}
    (himprove :
      StrongClusterRoutingImprovementStatement.{u}
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          polynomialGridMinorTreewidthBoundCleanResponder
              K b target ≤ treewidth G →
          ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_cleanResponderV2
    (strongClusterCleanActiveCutResponderV2_of_routingImprovement
      himprove)
    hc hreserve

end CutResponder
end Exponent7
end SimpleGraph
