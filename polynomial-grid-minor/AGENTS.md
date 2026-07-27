# AGENTS.md

## Mission

This directory formalizes the exponent-ten polynomial excluded-grid theorem:
every finite simple graph of sufficiently large treewidth
`O(g^10 polylog g)` contains a `g x g` grid minor.

The organizing Lean target is the direct degree-ten theorem using
`polynomialGridMinorTreewidthBound10`. The current public wrapper is not the
target proof because it weakens a contract-backed degree-nine theorem.

Read [README.md](README.md) for the mathematical architecture and source
inventory. Read [REMAINING.md](REMAINING.md) before selecting work; it is the
authoritative checklist for open proof obligations. Read [SKILLS.md](SKILLS.md)
for accumulated proof patterns and failure-avoidance rules.

## Most important rule

Work through a coherent proof package rather than stopping after one local
lemma. For substantial formalization, continue from definitions through the
proof-producing theorem and verification whenever the repository and papers
provide enough information. Stop only for a genuine mathematical ambiguity,
an unavailable dependency, a permission boundary, or an explicit instruction
to pause.

An interface reduction is useful progress, but it is not closure. Do not call a
component complete merely because a large proposition has been replaced by
smaller `Input`, `Provider`, or proof-data hypotheses.

## Non-negotiable proof standard

- Use Lean 4 and mathlib idioms.
- Use `SimpleGraph V` as the graph model already established in this project.
- Do not add `sorry`, `admit`, `unsafe`, `partial`, or a new project `axiom`.
- Existing contract axioms may be retained as statement documentation, but do
  not use them to discharge a theorem advertised as proved or self-contained.
- A final declaration is self-contained only when `#print axioms` contains no
  project-specific axiom and every semantic paper input has a Lean producer.
- Standard Lean dependencies such as `propext`, `Classical.choice`, and
  `Quot.sound` are acceptable.
- Keep theorem statements close enough to the source paper that a reviewer can
  compare hypotheses, constants, and conclusions directly.
- Encode asymptotic claims with explicit constants and powers, not `O(...)`
  notation in theorem statements.
- Preserve the natural-number convention for treewidth and document any
  additive constant caused by `bag.card - 1`.
- Keep imports narrow and use existing definitions rather than introducing a
  competing path, flow, minor, treewidth, or well-linkedness API.

## Scope discipline

The target is the exponent-ten Chuzhoy--Tan route.

- Do not formalize Chuzhoy--Tan Section 5 unless the user explicitly changes
  the target to the exponent-nine theorem.
- Do not derive the final result from the existing degree-nine contract route.
- For the degree-three sparsifier, formalize the semantic existential result
  needed downstream. Randomized running time, success probability as an
  algorithmic guarantee, and the `O(k^4)` vertex count are out of scope.
- For Chuzhoy Theorem 6.3, specialize to maximum degree three and the exact data
  consumed by `AppendixA3ClusterSplitInput`; a general algorithmic API for all
  degrees is unnecessary.
- Do not formalize both versions of the Chekuri--Chuzhoy paper. Use one proof
  and document the alternate theorem number.
- Do not remove unrelated contract axioms merely to reduce the global count.
  The completion criterion is the axiom closure of the direct degree-ten
  theorem.

## Source fidelity

The local PDFs are the source of truth for paper-level arguments. Record the
paper, theorem number, and any specialization in module comments for every
major theorem.

Important source notes:

- Chuzhoy--Tan Section 4, not Section 5, gives the
  `2^22 * q^10 * log q` crossbar threshold.
- Chuzhoy Theorem 6.3 is in `improved-bounds-chuzhoy.pdf`; its complete proof is
  Section 7.
- Chekuri--Chuzhoy theorem numbering differs between preprint and journal
  versions. Use the mapping in `README.md`.
- Chuzhoy--Tan's citation number for its Theorem 4.20 is inaccurate; the
  matching statement is preprint Theorem 2.11 or journal Theorem 2.14.
- Chuzhoy--Tan Lemma 3.3 is under-specified as printed. Its proof uses a
  crossbar in every matching-round cluster. Theorem 3.2 first stitches the odd
  clusters to obtain that situation. Formalize the corrected composition, not
  the defective standalone implication.
- Lemma 4.5 does not require the absent Robertson--Seymour source because
  Chuzhoy--Tan Appendix B gives the strengthened proof used here.

## File organization

- Lean proof files live in `statements-and-proofs/`.
- Local imports use `import «statements-and-proofs».ModuleName`.
- Keep definitions in the existing foundational modules and theorem-specific
  proof code in the corresponding proof module.
- Contract files state reviewable theorem interfaces. They must not become the
  implementation of completed results.
- Prefer adding a focused theorem near the existing interface it closes over
  creating another parallel hierarchy of wrappers.
- `PolynomialGridMinor.lean` is the aggregate import. Update it when adding a
  new public module.
- Put graph declarations under `SimpleGraph`; do not add an unrelated outer
  project namespace.
- Do not edit generated PDFs or extracted text files.
- Use ASCII in prose and identifiers unless Lean syntax or established
  mathematical notation gives a clear reason otherwise.

## Workflow for a proof package

1. Select an unchecked work package from `REMAINING.md` and identify its exact
   output declaration.
2. Read the corresponding paper section and the existing Lean definitions
   before changing the interface.
3. Audit which hypotheses are already theorems and which are still semantic
   assumptions. Do not duplicate proved work.
4. Implement the lowest missing mathematical lemma, then continue upward until
   the work package's output proposition is produced without new assumptions.
5. Compile every changed module and at least one downstream consumer.
6. Run `#print axioms` on a newly closed major theorem.
7. Update `REMAINING.md`: check only genuinely completed items, record the
   proof-producing theorem, and note the verification command.
8. Update `SKILLS.md` when an attempt exposes a reusable API, source, or
   no-progress pitfall.
9. Keep comments factual. State what remains rather than describing an input
   wrapper as an axiom-free proof skeleton.

When several independent packages are open, the A.1/A.2/A.3 source work,
Section 4 assembly, and Chekuri--Chuzhoy routing/stitching can proceed in
parallel. Keep edits in disjoint modules when using multiple workers.

## Verification

This directory is a standalone Lake project. Build it from this directory:

```bash
lake build
```

For trust-sensitive endpoints, rerun the checked-in audit:

```bash
lake env lean AxiomAudit.lean
```

The direct endpoint printed there is
`SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs10_and_cutMatchingGame`.

Before claiming completion, also scan the changed proof closure for accidental
placeholders and inspect the actual output of `#print axioms`. A successful
compile alone does not prove that a theorem avoided contract axioms.

## Status vocabulary

Use these terms consistently in comments and `REMAINING.md`:

- **Complete:** proved in Lean with no project axiom or semantic input in its
  transitive theorem closure.
- **Partial:** meaningful internal lemmas are proved, but a named construction
  or branch remains.
- **Input:** a proposition or structure that states the data a future proof
  must produce.
- **Contract-backed:** the declaration transitively uses a project axiom.
- **Blocked:** progress requires unavailable information or an external state
  change, and the exact blocker is recorded.

## Worktree safety

The worktree may contain user changes. Do not revert or rewrite unrelated work.
Keep edits scoped to the selected proof package and its documentation. Do not
rename modules or perform broad formatting changes while proving a local
result. Use non-destructive git commands and never discard another contributor's
changes.
