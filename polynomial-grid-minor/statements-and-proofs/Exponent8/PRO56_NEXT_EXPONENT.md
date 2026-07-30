# Pro 5.6 task: improve the exponent below eight-and-a-half

## Verified starting point

Read, in order:

1. `PRO56_READ_FIRST.md`;
2. `EXPONENT8_MAP.md`;
3. `RecursiveSlicing.lean`;
4. `ThreeRoundRecursion.lean`;
5. `ThreeRoundParameters.lean`;
6. `Section5Assembly.lean`;
7. `LocalDichotomy.lean`;
8. `GlobalDichotomy.lean`;
9. `NumericalEndpoint.lean`.

The current endpoint is:

```lean
SimpleGraph.Exponent8.polynomial_grid_minor_theorem_exponentEightAndHalf
```

It proves, with no project-specific axiom:

```text
treewidth G >= K * target^8 * sqrt(target) * (log_2 target)^b
  -> ContainsGridMinor G target.
```

The full Lake build and `Exponent8/AxiomAudit.lean` succeed.  Do not reprove
Observation 4.4 provenance, additive Lemma 4.8, LastHitCrossbar, strengthened
Claim 5.3, Observation 5.4, slicing composition, Section 5 assembly, or either
global grid-minor consumer.

## Exact source of the current half exponent

Write

```text
f = sqrt(g) + 1
L = log_2(g) + 1.
```

`ThreeRoundParameters.lean` uses:

```text
m0 = 64 * g^2 * f   * L
m1 = 32 * g^2 * f^2 * L
m2 = 16 * g^2 * f^3 * L
m3 =  8 * g^2 * f^4 * L
```

and:

```text
w3 = Theta(g^4)
w2 = O(g^5)
w1 = O(g^5 * sqrt(g))
w0 = O(g^6).
```

Thus both `m0*w0` and `m0*N`, with `N <= 64*g^6`, are

```text
O(g^8 * sqrt(g) * L).
```

The exponent eight is the present mass floor:

```text
N <= 64*g^6
assemblyMass = 32*N*g^2*L
finalPruning : 2*N*(4*g^2) <= Dhat*wFinal
Dhat = 32*g^4
mFinal >= 8*g^4*L.
```

The extra square-root comes from the initial slice count `m0`, not from the
global hairy-system or grid-minor consumers.

## First requested target: seven rounds and exponent eight-and-a-quarter

Stress-test and then formalize the following proposed generalization.

For `R = 7`, choose a rounding-safe fourth-root fanout `f4` satisfying:

```text
0 < f4
g^2 <= f4^8
f4 <= Croot * fourthRoot(g)
```

for power-of-two `g`.  Do not assume that
`sqrt (sqrt g) + 1` satisfies the required lower inequality without proving
all rounding cases.  Give the exact natural-number definition that does.

Use counts of the form:

```text
m_j = 2^(R + 3 - j) * g^2 * f4^(j+1) * L
```

so that:

```text
2*m_(j+1) <= m_j*f4
m_7 >= 8*g^4*L.
```

Choose seven row caps and eight widths satisfying, for every `j < 7`:

```text
2 * assemblyMass <= m_j * cap_j

2 * (f4*w_(j+1) + (f4+1)*cap_j + 4*g^4) <= w_j
```

together with:

```text
w_7 >= 16*g^4
2*N*(4*g^2) <= Dhat*w_7
```

The expected asymptotic accounting is:

```text
w_0 = O(g^6)
m_0 = O(g^2 * fourthRoot(g) * L)
localCost = O(g^8 * fourthRoot(g) * L).
```

Either prove this accounting with explicit division-free natural-number
formulas or identify the first incompatible inequality.

## Required Lean architecture

The current `recursiveSlicingRound` is already generic for one transition, but
`ThreeRoundRecursiveSlicingResult` and `threeRoundRecursiveSlicing` hard-code
three transitions.  Replace only this finite controller by a fixed-length or
list-indexed recursion theorem.  Preserve:

```text
RecursiveSlicingContext
RecursiveSliceLayer
LargeSliceLayer
RecursiveSliceLayer.observation54ExtendedParentRefinement
PathSlicing.composeSelectedSliceRefinements
RecursiveSliceLayer.weakPathOfSetsSystem_of_largeSliceLayer
RecursiveSliceLayer.weakPathOfSetsSystem_of_finalLayer
```

The desired new producer should specialize to seven rounds and feed the
unchanged local and global dichotomy consumers.

Propose exact declarations approximately of the form:

```lean
structure MultiRoundParameters ...

theorem recursiveSlicingRounds ...

def exponentEightQuarterLocalThreshold ...

theorem crossbarDichotomyInput825_proved ...

theorem polynomial_grid_minor_theorem_exponentEightAndQuarter ...
```

The final threshold should be displayed using a natural fourth-root operation,
with a proved comparison to `target^(1/4)`.  As in `NumericalEndpoint.lean`,
an intermediate `fourthRoot(target)+1` is acceptable if a constant-factor
lemma removes the `+1` for `target >= 2`.

## General fixed-round theorem

After the seven-round case, determine whether the same proof supports:

```text
R = 2^s - 1
fanout approximately g^(1 / 2^(s-1))
local exponent 8 + 1 / 2^(s-1).
```

Equivalently, for every fixed `s >= 1`, the expected exponent is:

```text
8 + 2/(R+1).
```

Give a proof or a counterexample from the exact recurrence.  Constants may
depend on `s`; no asymptotic constant may depend on `g`.

Also analyze the growing-round case.  The factor-two retention loss in every
round is harmless for fixed `R` but becomes polynomial when `R` grows with
`log g`.  Do not claim an exact exponent-eight theorem until this accumulated
loss is included.

## What would be required to go below exponent eight

With the current interfaces, `assemblyMass` is proportional to `N*g^2` and
`N` may be `Theta(g^6)`.  Therefore further fixed-depth slicing can approach
eight but cannot beat this mass floor.

To go below eight, identify which of the following must be strengthened:

1. the pseudo-grid row bound `N <= 64*g^6`;
2. the Theorem 4.11/4.15 assembly mass `Theta(N*g^2*log g)`;
3. the final `g^4` slice-count requirement;
4. the final pruning width forced by `Dhat = Theta(g^4)`; or
5. the target crossbar width `g^2`.

Do not modify the already proved exponent-eight-and-a-half endpoint while
investigating these alternatives.

## Relation to the published exponent-nine theorem

The published exponent-nine result is not a black-box input that can be
composed with the current proof to subtract another exponent.  Its Section 5
refinement corresponds, at the level of this recurrence, to the first
fixed-round improvement.  The present three-round proof replaces and extends
that internal refinement.

Starting from an implementation of the exponent-nine endpoint would save
formalization work, but applying the same three total rounds would still give
the current exponent eight-and-a-half.  A better exponent requires more total
rounds with reoptimized fanout, or a stronger mass/pruning theorem.  It does
not follow by feeding the exponent-nine theorem into the exponent-eight-and-a-
half theorem.
