# Polynomial Grid-Minor Theorem in Lean

This directory contains a Lean 4 formalization of the polynomial excluded-grid
argument of Chuzhoy and Tan. The immediate target is the weaker, exponent-ten
version of their Theorem 1.1:

```lean
theorem polynomial_grid_minor_theorem_degree10 :
    ∃ c1 c2 : ℕ, 0 < c1 ∧ 0 < c2 ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            polynomialGridMinorTreewidthBound10 c1 c2 g ≤ treewidth G →
              ContainsGridMinor G g
```

Here

```lean
polynomialGridMinorTreewidthBound10 c1 c2 g =
  c1 * g ^ 10 * (Nat.log 2 g) ^ c2
```

so the theorem is an explicit natural-number version of
`tw(G) >= O(g^10 polylog g)`. The goal is a semantically self-contained proof:
the final declaration may use Lean's standard logical axioms, but it must not
depend on a project `axiom`, a contract theorem, or an unproved proposition
standing for a paper result.

## Current status

The direct exponent-ten formalization is complete.

- The closed endpoint is
  `SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_proved`
  in `PolynomialGridMinorComplete.lean`.
- It instantiates the expanded source-route theorem with all nine proved
  producers and does not pass through the contract-backed degree-nine theorem.
- `#print axioms` for the closed endpoint and all three stable degree-ten
  wrappers reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Legacy project axioms remain declared as documentary contracts outside the
  direct theorem's transitive closure. The degree-nine theorem remains
  contract-backed and is not claimed as part of this completion.
- Work package 1A is closed: `routableSetFromTreewidth_proved` supplies
  `RoutableSetFromTreewidth 9 1 1 1` without project axioms.
- Work package 1B is closed:
  `exists_cutWellLinkedCoreFromRoutableSet_proved` supplies the low-degree,
  cut-well-linked core without project axioms. Its degree and reciprocal
  well-linkedness losses are both `O(eta * log k)`.
- Work package 1C has an axiom-free exponent-24 closure:
  `strongTreeOfSetsCoreFromNodeWellLinkedCore24_proved` produces the complete
  strong tree-of-sets system from the explicit
  `buildConstant24 * W * m^24 * Delta^10 * log_2(x)^5 < x` threshold. Bandwidth
  tree certificates, coherent connector
  restriction, scaled linked-subset routing, the two-stage strongification
  producer, full pendant-output transport, grouping/Hall consequences, dense
  finite-moment bounds, the named-multigraph Section 5 foundation, and the
  Hind--Oellermann deletion--contraction and Mader admissible split-off
  theorems are proved. Claims 5.14 and 5.15 now include exact support-edge
  thinning, finite root-to-leaf chain realization, varying root boundary
  subsets, scaling, integral extraction in the full-router-pruned network,
  host restoration, first-root-hit normalization, the specialized
  Corollary 2.12 root extraction, and the final three-way all-pairs
  concatenation. The finite-tree long-path/many-leaves choice, injective
  selected-leaf/root construction, global support-bundle transversal, and
  leaf-interface conclusion are also proved. The structural Phase 1 endpoint
  now returns either the Case-1 buffered support path or the complete Case-2
  all-pairs routing package. Quantitative parameter instantiation, Phase 2
  pruning and router production are assembled in the exponent-24 producer.
  The source-potential PARTITION/SEPARATE loop now proves the required
  good-router family directly, so the endpoint no longer uses the former
  CNS13 failed-router deletion contract. The Singh--Lau bounded-degree
  spanning-tree rounding theorem is proved in `SinghLauRounding.lean`.
- The direct degree-ten arithmetic, parameter selection, cut-matching game,
  expander-to-grid argument, and final graph-theoretic composition are proved.
- The most decomposed direct theorem exposes nine semantic inputs in
  `PolynomialGridMinor.lean` rather than hiding them behind axioms. WP1 is
  closed by `ChekuriChuzhoy.theoremA2SourceInputs_proved`, using the accepted
  `m^24` strong-tree threshold and the resulting `ell^50` path threshold.
- The documentary gap for Chuzhoy--Tan Appendix A.3 is resolved by the newly
  added `improved-bounds-chuzhoy.pdf`.
- Chuzhoy--Tan Theorem 2.3 is closed by
  `PolynomialGridMinor.exists_hairyPathOfSetsInput_proved`, which composes the
  proved A.1, A.2, and A.3/A.4 producers and has no project-specific axiom in
  its transitive closure.
- The strong path-of-sets-to-grid package is closed by
  `ChekuriChuzhoy.strongPathOfSets_containsGridMinor_proved`.
  `ChekuriChuzhoy.AppendixB1.theoremB1_proved` formalizes Appendix B,
  Theorem B.1, including the finite bump/cross and hill descents, the
  boundary-contact reconstruction, the terminal sparse-grid construction,
  and both page-60 type branches.  The resulting local-routing and Corollary
  3.2 producers have no project-specific axiom in their transitive closure.

See [REMAINING.md](REMAINING.md) for the dependency-ordered proof plan and
acceptance criteria. See [AGENTS.md](AGENTS.md) before changing Lean files and
[SKILLS.md](SKILLS.md) for accumulated formalization pitfalls.

## Proof architecture

The exponent-ten route is the following.

1. A degree-three treewidth sparsifier and the Chekuri--Chuzhoy
   treewidth-to-strong-path-of-sets theorem produce a strong path-of-sets
   system in a subcubic graph.
2. Chuzhoy's cluster-splitting theorem turns alternate clusters into the
   hairs required by Chuzhoy--Tan Theorem 2.3.
3. Chuzhoy--Tan Section 4 applies its `2^22 * q^10 * log q` pseudo-grid
   argument to each relevant cluster, producing either a crossbar or a minor
   with a large strong path-of-sets system.
4. A strong path-of-sets system gives a grid through Chekuri--Chuzhoy
   Corollary 3.3/3.4.
5. If every cluster gives a crossbar, the cut-matching construction produces
   an auxiliary expander, and the separator/minor theorem produces a grid.
6. Taking the internal power-of-two parameter
   `q = Theta(g * log(g)^(3/2))` yields `O(g^10 polylog g)`.

Chuzhoy--Tan Section 5 is needed only for the exponent-nine improvement and is
outside the current target.

## Repository layout

```text
polynomial-grid-minor/
  AGENTS.md
  AxiomAudit.lean
  lakefile.lean
  lake-manifest.json
  lean-toolchain
  PolynomialGridMinor.lean
  README.md
  REMAINING.md
  SKILLS.md
  statements-and-proofs/
    *.lean
  grid-minor-theorem.pdf
  treewidth-sparsifier.pdf
  chekuri-chuzhoy.pdf
  chekuri-chuzhoy-2.pdf
  improved-bounds-chuzhoy.pdf
  cut-matching-game.pdf
  expander.pdf
  menger.pdf
```

`PolynomialGridMinor.lean` is the aggregate import. Graph declarations live in
the root `SimpleGraph` namespace, with theorem-specific subnamespaces where
needed. Proof-module imports use `«statements-and-proofs».ModuleName`.

## Papers and their roles

| File | Role in the exponent-ten proof |
| --- | --- |
| `grid-minor-theorem.pdf` | Chuzhoy--Tan main proof. Use Theorem 2.3, Section 3, and the weaker Section 4 replacement for Theorem 3.1. Do not use Section 5. |
| `treewidth-sparsifier.pdf` | Theorem 1.1, used as Chuzhoy--Tan Theorem A.1. Only its existential degree-three topological-minor consequence is needed. |
| `chekuri-chuzhoy.pdf` | Preprint source for strong path-of-sets systems, path-of-sets to grid, local routing, and well-linkedness tools. |
| `chekuri-chuzhoy-2.pdf` | Journal version of the preceding paper. It is mathematically redundant but useful for matching published theorem numbers. |
| `improved-bounds-chuzhoy.pdf` | Chuzhoy, *Improved Bounds for the Excluded Grid Theorem*. Theorem 6.3 and its Section 7 proof supply Chuzhoy--Tan Theorem A.3. |
| `cut-matching-game.pdf` | Constant-expansion cut-matching game used in the all-crossbar branch. This branch is already formalized. |
| `expander.pdf` | Theorem 8.1 and its quadratic dependence on the separator parameter, used to turn the auxiliary expander into a grid minor. Already formalized. |
| `menger.pdf` | Documentary source for vertex and edge Menger. Both forms are already formalized locally. |

Numbering differs between the two Chekuri--Chuzhoy versions:

- The strong path-of-sets theorem is preprint Theorem 3.4 and journal
  Theorem 3.5.
- Path-of-sets to grid is preprint Corollary 3.3 and journal Corollary 3.4.
- The node-well-linked boost is preprint Theorem 2.11 and journal
  Theorem 2.14.
- The small-subset linking result is preprint Theorem 2.6 and journal
  Theorem 2.9.

## Build status

This directory is a standalone Lake package pinned to Lean `v4.30.0-rc2` and
Mathlib revision `ff96409d623285fbfe777cf47c50574f05f63a3d`. The treewidth
definitions and proof infrastructure are local in `TreewidthContract.lean` and
`Treewidth.lean`; no neighboring project is imported.

The Section 4 endpoint
`CrossbarTheorem.crossbar_or_strong_pathOfSets_minor_degree10_proved` is the
direct exponent-ten crossbar dichotomy: it uses the proved Theorem 4.1 and the
fully constructed pseudo-grid branch, not the degree-nine contract. Its axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Existing
linter warnings are non-blocking.  The completed WP6 endpoint
`ChekuriChuzhoy.strongPathOfSets_containsGridMinor_proved` has the same axiom
audit. The final source-route endpoint and the proof-facing, root-namespace,
and compatibility public wrappers also have exactly this standard-axiom
closure.

Build the complete development with:

```bash
cd polynomial-grid-minor
lake build
```

Rerun the trust report with:

```bash
lake env lean AxiomAudit.lean
```

## Definition of done

The exponent-ten formalization is complete only when all of the following
hold:

1. Every one of the nine direct source-route inputs has a theorem producing
   it from already proved Lean results.
2. The final theorem is obtained through the direct degree-ten route, not by
   weakening the contract-backed degree-nine theorem.
3. `#print axioms` for the final theorem reports no project axioms.
4. The public degree-ten wrappers point to the closed direct theorem.
5. A clean standalone `lake build` succeeds.
