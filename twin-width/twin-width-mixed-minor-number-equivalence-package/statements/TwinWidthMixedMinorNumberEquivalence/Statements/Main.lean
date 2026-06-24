import TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.FunctionalEquivalence
import TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Graph.MixedMinorNumber

namespace TwinWidthMixedMinorNumberEquivalence.Statements.Main

axiom twin_width_functionally_equivalent_mixed_minor_number :
    TwinWidth.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.twinWidth)
      (fun {V : Type} [Fintype V] [DecidableEq V] => TwinWidth.SimpleGraph.mixedMinorNumber)

end TwinWidthMixedMinorNumberEquivalence.Statements.Main
