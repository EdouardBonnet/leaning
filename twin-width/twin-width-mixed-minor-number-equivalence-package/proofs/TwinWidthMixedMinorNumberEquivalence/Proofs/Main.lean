import TwinWidth.Contraction.TwinWidth
import TwinWidth.Graph.MixedMinorNumber
import TwinWidthMixedMinorNumberEquivalence.Statements.Main

namespace TwinWidthMixedMinorNumberEquivalence.Proofs.Main

noncomputable def twinWidth : TwinWidthMixedMinorNumberEquivalence.Statements.Main.GraphParam :=
  fun {V} _ _ G => TwinWidth.SimpleGraph.twinWidth (V := V) G

noncomputable def mixedMinorNumber : TwinWidthMixedMinorNumberEquivalence.Statements.Main.GraphParam :=
  fun {V} _ _ G => TwinWidth.SimpleGraph.mixedMinorNumber (V := V) G

/-- Functional equivalence follows from the two submitted directional bounds. -/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    TwinWidthMixedMinorNumberEquivalence.Statements.Main.FunctionallyEquivalent
      TwinWidthMixedMinorNumberEquivalence.Statements.Main.twinWidth
      TwinWidthMixedMinorNumberEquivalence.Statements.Main.mixedMinorNumber := by
  constructor
  · exact TwinWidthMixedMinorNumberEquivalence.Statements.Main.twin_width_bounded_by_mixed_minor_number
  · refine ⟨fun d => 2 * (d + 3) + 2, ?_⟩
    intro V _ _ G
    exact TwinWidthMixedMinorNumberEquivalence.Statements.Main.mixed_minor_number_le_twin_width_linear G

end TwinWidthMixedMinorNumberEquivalence.Proofs.Main
