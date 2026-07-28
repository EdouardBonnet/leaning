import «statements-and-proofs».PolynomialGridMinorBound
import «statements-and-proofs».PolynomialGridMinorComplete

/-!
# Polynomial grid-minor theorem contract wrapper

This file exposes the contract-facing name for Theorem 1.1 of Chuzhoy--Tan,
"Towards tight(er) bounds for the Excluded Grid Theorem": there are constants
`c1, c2 > 0` such that treewidth at least `c1 * g^9 * log(g)^c2` forces a
`(g x g)` grid minor for every `g >= 2`.

The paper uses real-valued constants and asymptotic language in surrounding
discussion.  This contract uses natural-number constants and the explicit
base-two natural logarithm `Nat.log 2`; increasing the multiplicative constant
to a natural number preserves the theorem's implication form.

The degree-nine proof still lives in `«statements-and-proofs».PolynomialGridMinor`.
The direct degree-ten proof lives in
`«statements-and-proofs».PolynomialGridMinorComplete`.  This module keeps the
earlier contract namespace as a compatibility wrapper.
-/

namespace SimpleGraph
namespace PolynomialGridMinorContract

/-- Polynomial Excluded Grid Theorem, in the quantitative form of
Chuzhoy--Tan Theorem 1.1.

For every `g >= 2`, every finite simple graph whose treewidth is at least
`c1 * g^9 * (log_2 g)^c2` contains the `(g x g)` grid as a minor.
-/
theorem polynomial_grid_minor_theorem :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            polynomialGridMinorTreewidthBound c1 c2 g ≤ treewidth G →
              ContainsGridMinor G g :=
  _root_.SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem

/-- Direct exponent-ten compatibility form of the Polynomial Excluded Grid
Theorem. -/
theorem polynomial_grid_minor_theorem_degree10 :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {g : ℕ},
          2 ≤ g →
            polynomialGridMinorTreewidthBound10 c1 c2 g ≤ treewidth G →
              ContainsGridMinor G g :=
  _root_.SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem_degree10

end PolynomialGridMinorContract
end SimpleGraph
