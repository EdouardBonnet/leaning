import Mathlib.Data.Finset.Card
import TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

namespace TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree

open TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

noncomputable section

/-- The red degree of a bag, counted among the current bags of a trigraph
state. -/
def redDegree {V : Type} [DecidableEq V]
    (T : State V) (A : Finset V) : ℕ :=
  letI : DecidablePred (fun B => redAdj T A B) :=
    Classical.decPred (fun B => redAdj T A B)
  ((bags T).filter fun B => redAdj T A B).card

end

end TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree
