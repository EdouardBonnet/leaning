import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic

namespace TwinWidthTreewidthExponentialRedemption2.Statements.SingletonBags

noncomputable section

/-- The singleton-bag partition of a finite vertex type. -/
def singletonBags (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

end

end TwinWidthTreewidthExponentialRedemption2.Statements.SingletonBags
