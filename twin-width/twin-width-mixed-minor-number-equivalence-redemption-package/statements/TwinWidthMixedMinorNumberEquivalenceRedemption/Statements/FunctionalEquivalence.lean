import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.GraphParameter

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace FunctionalEquivalence

/-- Two finite simple-graph parameters are functionally equivalent when each is
bounded by a numerical function of the other. -/
def FunctionallyEquivalent (p q : GraphParameter.GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    p (V := V) G ≤ f (q (V := V) G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    q (V := V) G ≤ g (p (V := V) G))

end FunctionalEquivalence
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
