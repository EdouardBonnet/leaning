import «statements-and-proofs».Section45

/-!
# Rectangular Chuzhoy--Tan Theorem 4.15

The original formal theorem `Section45.theorem415` uses the same parameter
for the requested chain length and for the consecutive-overlap threshold.
The proof of Chuzhoy--Tan Theorem 4.15 does not require that specialization.

This module exposes the rectangular form needed by the exponent-seven
experiment: a chain of length `L` whose consecutive row sets overlap in at
least `W` rows.  The double-counting argument depends on `W`, while the final
weighted source-layer argument depends on `L`.

The explicit hypothesis `0 < W` is necessary for the theorem as stated over
natural numbers.  Without it, the degenerate choice
`N = D = M = 0`, `W = 0`, `L = 1` satisfies all three displayed numerical
inequalities but admits no one-element list in `Fin M`.
-/

namespace SimpleGraph
namespace Exponent7

open Finset

/-- Rectangular form of Chuzhoy--Tan Theorem 4.15.

The selected list has length `L`; consecutive selected row sets overlap in at
least `W` rows.  All inequalities are division-free natural-number
inequalities. -/
theorem theorem415_rectangular
    {N M D W L : ℕ} (S : Fin M → Finset (Fin N))
    (hW : 0 < W)
    (hN : 3 * W ≤ N)
    (hDsq : 4 * N * W ≤ D ^ 2)
    (hlarge : 2 * N * L ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (S i).card) :
    ∃ l : List (Fin M),
      l.length = L ∧
        l.IsChain (Section45.LargeOverlapRel S W) := by
  classical
  have hA : 0 < 2 * N := by omega
  have hind :
      ∀ I : Finset (Fin M),
        I ⊆ (Finset.univ : Finset (Fin M)) →
          Section45.RelIndependent (Section45.LargeOverlapRel S W) I →
            D * I.card < 2 * N := by
    intro I _ hI
    exact
      Section45.independent_bound_of_theorem415_hypotheses
        S hW hN hDsq hcard I hI
  rcases Section45.exists_relChainIn_of_weighted_independent_bound
      (rel := Section45.LargeOverlapRel S W)
      (s := (Finset.univ : Finset (Fin M)))
      (A := 2 * N) (D := D) (n := L)
      hA hind (by simpa using hlarge) with
    ⟨l, hlen, hchain, _⟩
  exact ⟨l, hlen, hchain⟩

end Exponent7
end SimpleGraph
