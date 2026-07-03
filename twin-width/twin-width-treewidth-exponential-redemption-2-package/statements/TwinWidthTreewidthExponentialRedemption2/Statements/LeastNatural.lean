import Mathlib.Data.Nat.Find

namespace TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural

noncomputable section

/-- The least natural number satisfying a predicate, with fallback value `0`
when the predicate is never satisfied. -/
def leastNat (P : ℕ → Prop) : ℕ :=
  letI : Decidable (∃ n, P n) := Classical.propDecidable _
  letI : DecidablePred P := Classical.decPred P
  if h : ∃ n, P n then Nat.find h else 0

end

end TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural
