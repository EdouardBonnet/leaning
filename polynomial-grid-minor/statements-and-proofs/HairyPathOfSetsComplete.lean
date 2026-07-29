import «statements-and-proofs».PolynomialGridMinor
import «statements-and-proofs».TreewidthSparsifierTheorem11
import «statements-and-proofs».AppendixA3Complete

/-!
# Chuzhoy--Tan Theorem 2.3

This module closes work package 4 by supplying the proved Appendix A.2
composition with:

* the axiom-free degree-three sparsifier from work package 2;
* the axiom-free Chekuri--Chuzhoy A.2 source package from work package 1; and
* the axiom-free Appendix A.3/A.4 cluster split from work package 3.

The resulting theorem is the direct degree-three hairy path-of-sets statement
used by the exponent-ten proof.
-/

namespace SimpleGraph
namespace PolynomialGridMinor

universe u

/-- Chuzhoy--Tan Theorem 2.3, with all three paper inputs supplied by their
Lean producers and no project-specific axiom in the transitive closure. -/
theorem exists_hairyPathOfSetsInput_proved :
    ∃ cHair cHairLog : ℕ,
      0 < cHair ∧
        0 < cHairLog ∧
          HairyPathOfSetsInput.{u} cHair cHairLog :=
  exists_hairyPathOfSetsInput_of_A1omega_ChekuriChuzhoy_theoremA2SourceInputs_and_appendixA4
    DegreeThreeStrongPathOfSetsContract.degreeThreeTreewidthSparsifierOmega_proved
    ChekuriChuzhoy.theoremA2SourceInputs_proved
    ⟨AppendixA3Complete.cSplit, AppendixA3Complete.cSplit_pos,
      AppendixA3Complete.appendixA4SplitInput⟩

end PolynomialGridMinor
end SimpleGraph
