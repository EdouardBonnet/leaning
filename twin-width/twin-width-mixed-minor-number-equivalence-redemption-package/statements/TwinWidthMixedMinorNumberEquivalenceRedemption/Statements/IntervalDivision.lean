import Mathlib.Data.Finset.Basic

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace IntervalDivision

/-- A k-division of Fin n is a partition into k nonempty consecutive
parts, ordered by their indices. -/
def Division (n k : ℕ) : Type :=
  { parts : Fin k → Finset (Fin n) //
    (∀ i, (parts i).Nonempty) ∧
    (∀ ⦃i j : Fin k⦄, i ≠ j → Disjoint (parts i) (parts j)) ∧
    (∀ x : Fin n, ∃ i : Fin k, x ∈ parts i) ∧
    (∀ i ⦃a b c : Fin n⦄,
      a ∈ parts i → c ∈ parts i → a ≤ b → b ≤ c → b ∈ parts i) ∧
    (∀ ⦃i j : Fin k⦄, i < j →
      ∀ ⦃a b : Fin n⦄, a ∈ parts i → b ∈ parts j → a < b) }

/-- The ordered family of parts of an interval division. -/
def part {n k : ℕ} (D : Division n k) : Fin k → Finset (Fin n) :=
  Subtype.val D

end IntervalDivision
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
