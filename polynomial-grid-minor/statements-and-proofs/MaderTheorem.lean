import «statements-and-proofs».MaderEvenTheorem
import «statements-and-proofs».MaderOddReduction

/-!
# Mader's admissible split-off theorem

This combines the even theorem with the three-parallel-edge reduction for odd
degree.  Degree three is the classical exceptional case.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton

universe u

namespace FiniteEdgeIndexedGraph

/-- The fully proved named-multigraph admissible-pair theorem used by the
Chekuri--Chuzhoy terminal-skeleton construction. -/
theorem maderAdmissiblePair : MaderAdmissiblePairStatement.{u} := by
  intro W _ _ H s hdegree hneThree hno
  rcases Nat.even_or_odd (H.degree s) with heven | hodd
  · exact H.exists_maderAdmissible_of_even s hdegree heven hno
  · have hfive : 5 ≤ H.degree s := by
      rcases hodd with ⟨d, hd⟩
      omega
    let hevenExists : EvenMaderPairExistence (W := W ⊕ Unit) := by
      intro K center htwo hevenK hnoK
      exact K.exists_maderAdmissible_of_even center htwo hevenK hnoK
    exact H.exists_maderAdmissible_of_odd hevenExists s hfive hodd hno

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph
