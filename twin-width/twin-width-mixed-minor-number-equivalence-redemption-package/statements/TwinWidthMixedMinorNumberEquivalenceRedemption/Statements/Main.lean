import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.FunctionalEquivalence
import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph
import TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Main

open TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
open TwinWidthTreewidthExponentialRedemption2.Statements

/-- Twin-width, using the definition imported from the Redemption 2
treewidth-exponential submission, and the graph mixed minor number defined in
this submission are functionally equivalent finite-graph parameters. -/
axiom functionalEquivalence :
    FunctionalEquivalence.FunctionallyEquivalent
      (fun {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] =>
        TwinWidth.twinWidth G)
      (fun {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] =>
        SimpleGraph.mixedMinorNumber G)

end Main
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
