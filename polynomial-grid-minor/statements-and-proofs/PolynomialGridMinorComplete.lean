import «statements-and-proofs».PolynomialGridMinor
import «statements-and-proofs».TreewidthSparsifierTheorem11
import «statements-and-proofs».ChekuriChuzhoyTheoremA2Inputs
import «statements-and-proofs».AppendixA3Complete
import «statements-and-proofs».Section4Complete
import «statements-and-proofs».ChekuriChuzhoyWP6Complete

/-!
# Direct exponent-ten polynomial grid-minor theorem

This module performs the final source-route assembly for Chuzhoy--Tan,
"Towards tight(er) bounds for the Excluded Grid Theorem."  It instantiates
the expanded direct degree-ten frontier with all nine proved producers:

* the degree-three treewidth sparsifier;
* routable terminals, a cut-well-linked core, the strong tree-of-sets
  construction, and leafy-tree extraction;
* the Appendix A.3 cluster split;
* the Section 4 weak-to-strong crossbar branch;
* the Chekuri--Chuzhoy local routing theorem; and
* the Chekuri--Chuzhoy stitching theorem.

The result follows the `g^10` source route directly.  It does not use the
separate contract-backed degree-nine theorem.
-/

namespace SimpleGraph
namespace PolynomialGridMinor

universe u

/-- The direct exponent-ten polynomial excluded-grid theorem, with every
paper-level input discharged by its Lean producer. -/
theorem polynomial_grid_minor_theorem_degree10_proved :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  _root_.SimpleGraph.polynomial_grid_minor_theorem_degree10_of_A1omega_ChekuriChuzhoy_routable_cutMatching_treeCore_leafExtraction_A3_section4WeakToStrong_cutMatchingGame_and_localRoutingCluster_stitching
    DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_proved
    ChekuriChuzhoy.exists_routableSetFromTreewidth_proved
    ChekuriChuzhoy.exists_cutWellLinkedCoreFromRoutableSet_proved
    ChekuriChuzhoy.exists_strongTreeOfSetsCoreFromNodeWellLinkedCore_proved
    ChekuriChuzhoy.strongPathOfSetsFromLeafyStrongTreeOfSets_proved
    ⟨AppendixA3Complete.cSplit, AppendixA3Complete.cSplit_pos,
      AppendixA3Complete.appendixA3ClusterSplitInput⟩
    ⟨20000, by norm_num,
      Section4Assembly.section4WeakToStrongAssemblyInput10_proved⟩
    ChekuriChuzhoy.localRoutingClusterInput_proved
    ChekuriChuzhoy.stitchingInput_proved

/-- Stable proof-facing name for the direct exponent-ten theorem. -/
theorem polynomial_grid_minor_theorem_degree10 :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_degree10_proved

end PolynomialGridMinor

/-- Public direct exponent-ten polynomial excluded-grid theorem. -/
theorem polynomial_grid_minor_theorem_degree10 :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBound10 c1 c2 target ≤ treewidth G →
              ContainsGridMinor G target :=
  PolynomialGridMinor.polynomial_grid_minor_theorem_degree10

end SimpleGraph
