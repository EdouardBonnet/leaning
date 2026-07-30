# Conditional exponent-seven route

This directory implements the exponent-seven program requested after the
completed exponent-eight-and-a-half endpoint.

The formalized chain includes:

- rectangular Theorem 4.15 and its Section 5 assembly;
- additive-loss logarithmic-depth recursive slicing;
- the clean bridge-batch theorem;
- exact alternating prescribed matchings and their grid-minor geometry;
- the short-wide strong Path-of-Sets consumer;
- the uniform pseudo-grid and local crossbar-or-grid dichotomy;
- propagation through hairy Path-of-Sets Systems and the proved
  cut-matching-game assembly; and
- a complete numerical endpoint with threshold
  `K * g^7 * (log_2 g)^b`.

The final declaration is:

```lean
SimpleGraph.Exponent7.polynomial_grid_minor_theorem7
```

It takes two ordinary arguments:

```lean
hDichotomy : CleanMatchingDichotomyStatement reserve
hreserve   : 0 < reserve
```

and returns the exponent-seven excluded-grid theorem.  The proposition
argument is intentional: prescribed endpoint control for a simultaneous
matching is the genuinely new graph-theoretic ingredient identified by the
Pro 5.6 audit.  It is not declared as an axiom.  Consequently `#print axioms`
for the conditional endpoint reports only Lean's standard logical axioms.

Run:

```bash
lake build '«statements-and-proofs».Exponent7.NumericalEndpoint'
lake env lean statements-and-proofs/Exponent7/AxiomAudit.lean
```

The package becomes an unconditional exponent-seven theorem exactly when a
Lean proof of `CleanMatchingDichotomyStatement reserve` is supplied for some
positive constant `reserve`.
