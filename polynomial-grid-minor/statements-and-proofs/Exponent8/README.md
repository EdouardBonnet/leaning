# Experimental exponent-eight route

This directory is intentionally outside the aggregate
`PolynomialGridMinor.lean` import.  It prepares a three-round recursive
version of Chuzhoy--Tan Section 5 without changing the proved degree-ten
endpoint.

The current modules are:

- `Lemma48Additive.lean`: the exact additive loss hidden in the existing
  Lemma 4.8 pruning proof;
- `LastHitSelection.lean`: bounded-fiber counting and distinct
  representative selection;
- `LastHitCrossbar.lean`: contracted-slice provenance, uncontracting,
  orientation toward `X`, last-hit truncation, and the crossbar construction;
- `Observation44RootProvenance.lean`: exact row--auxiliary incidence through
  both legal Observation 4.4 contractions, rooted finite descent, and the
  full-source-row producer for `SliceLocalizationInvariant`;
- `RootedSection42.lean`: rooted Observation 4.4 plus Theorem 4.6 and
  additive per-slice cleanup, packaged as the initial
  `RecursiveSliceLayer`;
- `Claim53Strong.lean`: the strengthened Claim 5.3 loss
  `|Q_bad| < 4 * g^4`;
- `RecursiveSlicing.lean`: the explicit three-round data and the single
  allowed placeholder for the later recursive composition theorem;
- `AxiomAudit.lean`: the focused trust audit.

The exact existing Section 4 declarations and the still-missing source
dependencies are recorded in `../../EXPONENT8_MAP.md`.

Nothing in this directory should be imported by the public endpoint until the
recursive slicing placeholder has been discharged and the resulting numerical
assembly has been reviewed.
