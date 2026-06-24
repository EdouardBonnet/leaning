import Mathlib.Combinatorics.SimpleGraph.Basic

namespace TwinWidthMixedMinorNumberEquivalence.Statements.Main

def GraphParam :=
  ∀ {V : Type}, [Fintype V] → [DecidableEq V] → SimpleGraph V → Nat

def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : Nat → Nat, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    p (V := V) G ≤ f (q (V := V) G)) ∧
  (∃ g : Nat → Nat, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    q (V := V) G ≤ g (p (V := V) G))

axiom twinWidth : GraphParam

axiom mixedMinorNumber : GraphParam

axiom twin_width_bounded_by_mixed_minor_number :
    ∃ f : Nat → Nat, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      twinWidth (V := V) G ≤ f (mixedMinorNumber (V := V) G)

axiom mixed_minor_number_le_twin_width_linear
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    mixedMinorNumber (V := V) G ≤ 2 * (twinWidth (V := V) G + 3) + 2

axiom twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent twinWidth mixedMinorNumber

end TwinWidthMixedMinorNumberEquivalence.Statements.Main
