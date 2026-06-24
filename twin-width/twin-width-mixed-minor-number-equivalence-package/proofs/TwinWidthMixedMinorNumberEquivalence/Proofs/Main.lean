import TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.MainContract
import TwinWidthMixedMinorNumberEquivalence.Statements.Main

namespace TwinWidthMixedMinorNumberEquivalence.Proofs.Main

theorem twin_width_functionally_equivalent_mixed_minor_number :
    TwinWidth.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.mixedMinorNumber) :=
  TwinWidth.MainContract.twin_width_functionally_equivalent_mixed_minor_number

end TwinWidthMixedMinorNumberEquivalence.Proofs.Main
