import «statements-and-proofs».ChekuriChuzhoyCorollary32Contract

/-!
# Statement for Chekuri--Chuzhoy Corollary 3.3

Corollary 3.3 is the path-of-sets-to-grid statement at the exact parameters
used by Chekuri--Chuzhoy: width `16 * g^2 + 10 * g` and length
`2 * g * (g - 1)` force a `g x g` grid minor.

The repository now uses the split, proof-facing inputs in
`«statements-and-proofs».ChekuriChuzhoy` instead of postulating this broad statement as
an axiom.  This file keeps the statement visible without adding an assumption.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyContract

universe u

/-- Chekuri--Chuzhoy Corollary 3.3, structural form. -/
def Corollary33Statement : Prop :=
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {g : ℕ},
        2 ≤ g →
          PathOfSetsSystem G (2 * g * (g - 1)) (16 * g ^ 2 + 10 * g) →
            ContainsGridMinor G g

end ChekuriChuzhoyContract
end SimpleGraph
