import TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.Main

/-!
# Contract statement for the main equivalence theorem

This file exposes the final graph-parameter statement: twin-width and mixed
minor number are functionally equivalent for finite simple graphs.
-/

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth
namespace MainContract

/-- Twin-width and mixed minor number are functionally equivalent finite-graph
parameters. -/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent SimpleGraph.twinWidth SimpleGraph.mixedMinorNumber := by
  exact TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.twinWidth_functionallyEquivalent_mixedMinorNumber

end MainContract
end TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth
