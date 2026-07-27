import «statements-and-proofs».RoutableSetFromNodeWellLinkedProducer
import «statements-and-proofs».CutWellLinkedCoreProducer
import «statements-and-proofs».ChekuriChuzhoyTheorem46
import «statements-and-proofs».ChekuriChuzhoyTheorem221

/-!
# Closed source inputs for Chekuri--Chuzhoy Theorem A.2

This module is the package-level endpoint for WP1.  It combines the proved
Lemma 2.17 route, the routed cut-matching construction, the accepted
`m^24` Section 4 strong-tree construction, and the source-faithful DFS proof
of Theorem 4.6.  The corresponding path threshold is `ell^50`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy

universe u

/-- All four proof-producing components of the expanded A.2 boundary. -/
theorem theoremA2LeafSourceInputs_proved :
    TheoremA2LeafSourceInputs.{u} :=
  ⟨exists_routableSetFromTreewidth_proved,
    exists_cutWellLinkedCoreFromRoutableSet_proved,
    exists_strongTreeOfSetsCoreFromNodeWellLinkedCore_proved,
    strongPathOfSetsFromLeafyStrongTreeOfSets_proved⟩

/-- WP1 acceptance endpoint: Chekuri--Chuzhoy A.2 source inputs with no
project axiom in their transitive closure. -/
theorem theoremA2SourceInputs_proved :
    TheoremA2SourceInputs.{u} :=
  theoremA2SourceInputs_of_leafSourceInputs
    theoremA2LeafSourceInputs_proved

end ChekuriChuzhoy
end SimpleGraph
