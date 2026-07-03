import Mathlib.Data.Finset.Card

namespace TwinWidthTreewidthExponentialRedemption.Statements.RedDegree

noncomputable section

/-- The red degree of a bag, counted among the current bags of a trigraph state. -/
def redDegree {V : Type} [DecidableEq V]
    (bags : Finset (Finset V)) (redAdj : Finset V → Finset V → Prop)
    (A : Finset V) : ℕ := by
  classical
  exact (bags.filter fun B => redAdj A B).card

end

end TwinWidthTreewidthExponentialRedemption.Statements.RedDegree
