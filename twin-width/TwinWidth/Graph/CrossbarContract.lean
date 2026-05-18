import TwinWidth.Graph.Crossbar
import TwinWidth.Graph.CrossbarPower
import TwinWidth.Graph.PathOfSets
import TwinWidth.Graph.Minor
import TwinWidth.Graph.Degree
import Mathlib.Data.Nat.Log

/-!
# Contract for the crossbar dichotomy

This file states Chuzhoy--Tan Theorem 3.1 in the language of the formalized
objects: from three large terminal sets `A`, `B`, and `X` with the two required
linkage packings, either a crossbar exists or a minor contains a large strong
Path-of-Sets System.
-/

namespace TwinWidth
namespace SimpleGraph
namespace CrossbarContract

/-- `G` has a minor that contains a strong Path-of-Sets System of length `ell`
and width `w`. -/
def HasStrongPathOfSetsMinor {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (ell w : ℕ) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
    (H : _root_.SimpleGraph W),
      IsMinor H G ∧ Nonempty (StrongPathOfSetsSystem H ell w)

/-- Chuzhoy--Tan Theorem 3.1, stated as a contract.

The constant `c` absorbs the `Ω(g^2)` lower bounds in the path-of-sets outcome:
`g^2 ≤ c * ell` and `g^2 ≤ c * w`.
-/
axiom crossbar_or_strong_pathOfSets_minor :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (H : _root_.SimpleGraph V) {g kappa : ℕ}
        {A B X : Finset V},
          2 ≤ g →
            IsPowerOfTwo g →
              A.card = kappa →
                B.card = kappa →
                  X.card = kappa →
                    Disjoint A B →
                      Disjoint A X →
                        Disjoint B X →
                          2 ^ 22 * g ^ 9 * Nat.log 2 g ≤ kappa →
                            (∀ x ∈ X, DegreeEquals H x 1) →
                              (Pab : PathPacking H A B) →
                                Pab.card = kappa →
                                  (Pax : PathPacking H A X) →
                                    Pax.card = kappa →
                                      Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                        ∃ ell w : ℕ,
                                          g ^ 2 ≤ c * ell ∧
                                            g ^ 2 ≤ c * w ∧
                                              HasStrongPathOfSetsMinor H ell w

end CrossbarContract
end SimpleGraph
end TwinWidth
