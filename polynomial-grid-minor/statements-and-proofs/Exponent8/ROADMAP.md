# Exponent-eight-and-a-half roadmap

## Completed proof chain

- additive Lemma 4.8;
- rooted Observation 4.4 contraction provenance;
- last-hit crossbar and strengthened Claim 5.3;
- Observation 5.4, including exact support subtypes and hereditary unique
  linkage;
- nonconsecutive slicing composition;
- all three recursive rounds;
- explicit `2^29 * g^8 * sqrt(g) * (log_2(g)+1)` local parameters;
- all-happy-cluster retention in large slices;
- corrected dyadic grouping;
- parent-ordered Theorem 4.15 assembly;
- all three majority-large exits;
- the all-small terminal exit; and
- the actual pseudo-grid producer
  `exists_reduced_weakPathOfSetsSystem_threeRound`;
- the factor-eight pseudo-grid budget and complementary crossbar branch;
- the local crossbar/strong-minor dichotomy at the exact threshold
  `2^29 * g^8 * sqrt(g) * (log_2(g)+1)`;
- transport of the strong minor through the Observation 4.4 reduction and
  every hairy cluster;
- the odd-cluster cut-matching-game grid assembly;
- the proved Chekuri--Chuzhoy grid consumer for the strong-minor branch;
- the parameterized treewidth theorem
  `containsGridMinor_of_treewidth_parameters85`;
- explicit target-dependent choices of `ell`, `w`, `k`, `g`, and `r`;
- a target-independent coefficient template satisfying every numerical
  inequality; and
- the closed exact-form theorem
  `polynomial_grid_minor_theorem_exponentEightAndHalf`.

Every item above is proved in Lean without a project-specific axiom.

## Current experimental endpoint

The first exponent-eight-and-a-half milestone is complete.  The local
declaration

```text
crossbarDichotomyInput85_proved
```

uses exactly the threshold

```text
2^29 * g^8 * sqrt(g) * (log_2(g)+1)
```

and returns either a width-`g^2` crossbar or a strong Path-of-Sets minor at
scale `g^2 / 20000`.  `GlobalDichotomy.lean` discharges both outcomes and
proves `containsGridMinor_of_treewidth_parameters85`.

`NumericalEndpoint.lean` then proves

```lean
theorem polynomial_grid_minor_theorem_exponentEightAndHalf :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {target : ℕ},
          2 ≤ target →
            polynomialGridMinorTreewidthBoundEightAndHalf
                K b target ≤ treewidth G →
              ContainsGridMinor G target
```

where

```text
polynomialGridMinorTreewidthBoundEightAndHalf K b target
  = K * target^8 * sqrt(target) * (log_2 target)^b.
```

The proof first establishes a uniform bound with `sqrt(target)+1`, then
doubles the coefficient to obtain the displayed exact square-root form.

## Remaining work after the 8.5 milestone

1. Independently review the chosen constants and each source hypothesis.
2. Decide whether to expose this theorem through the public aggregate and
   replace the existing public polynomial endpoint.
3. If a lower exponent is desired, isolate the next mathematical improvement
   in a new experimental package; do not reopen the completed Section 5
   recursion without a source-level reason.
