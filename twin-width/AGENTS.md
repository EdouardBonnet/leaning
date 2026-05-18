# AGENTS.md

## Most important operating rule

- Work autonomously for long uninterrupted stretches. For substantial proof,
  implementation, or formalization tasks, do a larger coherent chunk of work
  before terminating: continue for at least one hour before stopping unless
  there is a concrete reason to stop, such as an explicit design uncertainty
  that cannot be resolved from the repository or papers, a safety/permission
  blocker, an external dependency blocker, or a direct user instruction to
  pause. Do not stop merely because one small lemma, local edit, or verification
  step is complete; if there is no real blocker, keep going.

## Project mission

This repository formalizes, in Lean 4 using mathlib, the theorem that **twin-width** and **mixed minor number** are functionally equivalent graph parameters for finite simple graphs.

Treat the main theorem as the organizing objective:

```lean
theorem twinWidth_functionallyEquivalent_mixedMinorNumber :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  -- proof
```

The development should build the definitions and intermediate lemmas needed to make this theorem precise and provable. Do not spend effort on unrelated graph theory unless it directly supports this target.

## Ground rules

- Use Lean 4 and mathlib idioms.
- Use `SimpleGraph V` as the base graph model.
- Do not create a competing simple graph hierarchy.
- Do not add `unsafe`, `admit`, or completed-file `sorry`.
- Do not add `axiom` outside files whose names end in `Contract.lean`.
- Do not encode asymptotic notation such as `2^(2^O(k))` as a final theorem.
- Use either explicit bounding functions or existential bounding functions.
- Keep imports narrow.
- Prefer stable, reusable definitions over tactic-heavy one-off proofs.
- Run the relevant Lean command before claiming a file compiles.
- If a mathematical convention changes a constant, document the convention and update theorem names/comments accordingly.
- Distinguish definition-only files from files that prove lemmas.
- For every major lemma/theorem family, make a `Contract.lean` file with axioms
  for the targeted statements and only the definitions/imports needed to state
  them. The statements should read as closely as possible to the natural
  language theorem.
- Give contract axioms meaningful theorem-style names and state the claim
  directly with quantifiers, hypotheses, and conclusions. Avoid axioms whose
  entire statement is just a proposition-wrapper alias such as
  `SomeBoundedByOther someBoundFunction`; those wrappers may still exist as
  helper definitions, but the contract itself should be human-readable.
- Each contract file should expose only the main final lemma for the proof
  module. Do not include intermediate variants such as ordered-matrix forms,
  greedy-step forms, counting sublemmas, or conversion steps in contract files
  unless that file's sole purpose is proving that final statement.
- Each contract axiom should have a corresponding fully formalized theorem in
  the full proof file once that item is proved. Contract modules should not be
  imported to discharge completed proofs.

## Target mathematical statement

The literature states the equivalence in the following quantitative shape for finite graphs:

```text
(mxn(G) - 1) / 2 ≤ tww(G) ≤ 2^(2^O(mxn(G)))
```

In Lean, formalize this as two directional bounds and then combine them into functional equivalence.

Recommended high-level definitions:

```lean
def GraphParam := ∀ {V : Type*}, [Fintype V] → [DecidableEq V] → SimpleGraph V → ℕ

/-- Two graph parameters are functionally equivalent when each is bounded
by some numerical function of the other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    p G ≤ f (q G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    q G ≤ g (p G))
```

Adjust the exact signature only when the formal definitions require it. For example, add `[DecidableRel G.Adj]` locally if the matrix construction needs it.

## Definitions to build

### 1. Finite orderings and divisions

Define an ordering of a finite vertex type, preferably through an equivalence with `Fin n` or through a structure that exposes a linear order and cardinality.

Define a `k`-division of `Fin n` as a partition into `k` nonempty consecutive intervals. A cut-point representation is usually easier than a set-of-sets representation.

Required API:

```lean
Division.part
Division.part_nonempty
Division.part_disjoint
Division.part_cover
Division.part_convex
```

Names can differ if they are clearer, but keep them descriptive.

### 2. Boolean matrices and mixed minors

Use mathlib matrices where practical:

```lean
Matrix (Fin n) (Fin m) Bool
```

Define cells determined by row and column divisions. A cell is mixed if it contains both `true` and `false` entries.

Expected concepts:

```lean
CellMixed M R C i j
HasMixedMinor M k
matrixMixedNumber M
```

Watch the `k = 0` convention. State it explicitly in comments and ensure monotonicity/bounds lemmas use the same convention.

### 3. Graph mixed minor number

For `G : SimpleGraph V`, define an ordered adjacency matrix for each vertex ordering. Then define:

```lean
mixedMinorNumber G
```

as the minimum matrix mixed number over all orderings of `V`.

Required lemmas:

```lean
mixedMinorNumber_le_orderedAdjacencyMixedNumber
exists_order_mixedNumber_eq_mixedMinorNumber
mixedMinorNumber_le_card
mixedMinorNumber_congr
```

The `congr` theorem should express invariance under graph isomorphism or relabeling.

### 4. Trigraphs and contraction sequences

Use a representation that avoids changing vertex types at every contraction. Prefer a partition of the original vertex set into current bags.

Define:

```lean
TrigraphState
redAdj
blackAdj
redDegree
contractState
ContractionSequence
HasTwinWidthAtMost G d
twinWidth G
```

A contraction sequence should start from singleton bags representing `G` and end in one bag. Its width is the maximum red degree over all intermediate states.

Required lemmas:

```lean
hasTwinWidthAtMost_mono
twinWidth_le_of_hasTwinWidthAtMost
hasTwinWidthAtMost_twinWidth
empty_twinWidth_eq_zero
complete_twinWidth_eq_zero
```

Only add examples after the core definitions compile.

### 5. Direction: twin-width implies bounded mixed minor number

Formalize the extraction of a good vertex ordering from a bounded-width contraction sequence, or the equivalent matrix argument.

Target theorem shape:

```lean
theorem mixedMinorNumber_le_of_twinWidth_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    mixedMinorNumber G ≤ 2 * twinWidth G + 2 := by
  -- proof
```

The additive constant depends on conventions. Do not force this exact constant if the definitions naturally give `+1`, `+2`, or a nearby bound. Use a theorem name that remains true after the constant is chosen.

### 6. Direction: mixed minor number implies bounded twin-width

Define an explicit function once the construction is formalized:

```lean
def twinWidthBoundOfMixedMinorNumber : ℕ → ℕ :=
  -- explicit elementary bound
```

Then prove:

```lean
theorem twinWidth_le_of_mixedMinorNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  -- proof
```

Until the explicit quantitative proof is available, it is acceptable in draft modules to prove a qualitative theorem with an existential bounding function, but do not mark it complete with placeholders.

### 7. Main equivalence

Combine the two directional theorems:

```lean
theorem twinWidth_functionallyEquivalent_mixedMinorNumber :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  constructor
  · exact ⟨twinWidthBoundOfMixedMinorNumber, twinWidth_le_of_mixedMinorNumber⟩
  · refine ⟨fun d => 2 * d + 2, ?_⟩
    intro V _ _ G
    simpa using mixedMinorNumber_le_of_twinWidth_le G
```

This sketch may need binder-order adjustments after `GraphParam` is finalized.

## File layout

Use this layout unless the user requests another one:

```text
TwinWidth/
  Order/
    Intervals.lean
    Divisions.lean
  Matrix/
    BoolMatrix.lean
    OrderedAdjacency.lean
    Cell.lean
    Mixed.lean
    MixedMinor.lean
    MixedNumber.lean
  Graph/
    OrderedGraph.lean
    MixedMinorNumber.lean
  Contraction/
    Trigraph.lean
    Partition.lean
    Contract.lean
    Sequence.lean
    RedDegree.lean
    TwinWidth.lean
  Equivalence/
    FunctionalEquivalence.lean
    TwinWidthToMixed.lean
    MixedToTwinWidth.lean
    Main.lean
  Examples.lean
  TwinWidth.lean
```

Public imports should go in `TwinWidth.lean`:

```lean
import TwinWidth.Graph.MixedMinorNumber
import TwinWidth.Contraction.TwinWidth
import TwinWidth.Equivalence.Main
import TwinWidth.Examples
```

## Namespace policy

Use:

```lean
namespace TwinWidth

namespace Matrix
-- Boolean matrix and mixed-minor declarations
end Matrix

namespace SimpleGraph
-- graph parameters for `SimpleGraph`
end SimpleGraph

end TwinWidth
```

Do not put project definitions directly in the root namespace.

## Imports

Start narrow. Common imports include:

```lean
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Interval.Finset.Nat
```

If an import fails, inspect the local mathlib version instead of guessing. Search the local `Mathlib/` tree.

## Proof style

Use clear Lean proof scripts. Prefer:

```lean
simp
simpa
rw
rwa
exact
apply
intro
constructor
rcases
obtain
refine
by_cases
classical
```

Use automation only when it makes the proof clearer. Avoid hiding mathematical invariants behind large `aesop` calls in the main equivalence proof.

When a proof becomes large, factor it into named lemmas that describe the mathematical invariant being used.

## Naming conventions

Use mathlib-style `lower_snake_case` names.

Good names:

```lean
cellMixed_iff_exists_true_and_false
hasMixedMinor_mono
matrixMixedNumber_le_min_card
mixedMinorNumber_le_card
redDegree_contract_le
hasTwinWidthAtMost_mono
twinWidth_le_of_hasTwinWidthAtMost
mixedMinorNumber_le_of_twinWidth_le
twinWidth_le_of_mixedMinorNumber
twinWidth_functionallyEquivalent_mixedMinorNumber
```

Avoid vague names:

```lean
main
lemma1
hard_direction
helper_final
```

## Documentation expectations

Every file should start with a module docstring explaining its role in the twin-width/mixed-minor equivalence proof.

Every nontrivial definition should have a docstring, especially:

- `Division`
- `CellMixed`
- `HasMixedMinor`
- `matrixMixedNumber`
- `mixedMinorNumber`
- `TrigraphState`
- `ContractionSequence`
- `HasTwinWidthAtMost`
- `twinWidth`
- `FunctionallyEquivalent`

For hard lemmas, include an informal proof outline in comments before the theorem statement.

## Verification commands

After dependency setup:

```bash
lake exe cache get
```

For a single file:

```bash
lake env lean TwinWidth/Matrix/MixedMinor.lean
```

For the whole project:

```bash
lake build
```

Before handoff:

```bash
lake build
grep -R --line-number --include='*.lean' -E '\bsorry\b|\badmit\b|axiom ' TwinWidth \
  | grep -v 'Contract\.lean'
```

If the grep command reports placeholders or non-contract axioms in completed
files, remove them. Contract-file axioms are allowed only as explicit
interfaces for work that is not yet fully proved, and any remaining contract
axioms must be reported clearly.

## Completion criteria

A task is complete only when:

- all modified Lean files compile;
- no prohibited placeholders remain in completed files;
- definitions are documented;
- theorem statements match the conventions used in the definitions;
- directional bounds are stated separately before the final equivalence theorem;
- any remaining limitations are explicitly documented.

## Handling uncertainty

The equivalence theorem is convention-sensitive. When uncertainty arises:

1. identify the exact definition affected;
2. state the convention in a docstring;
3. prove lemmas using that convention;
4. avoid silently changing a theorem statement only to make a proof easier.

For example, if `HasMixedMinor M 0` is vacuous, downstream maximum and monotonicity lemmas may differ from a convention where mixed minors start at `1`. Choose one convention early and document it.

## Do not do these things

- Do not continue the old broad graph-theory roadmap unless specifically asked.
- Do not redefine `SimpleGraph`.
- Do not formalize multigraphs or directed graphs in the first pass.
- Do not use quotient-heavy definitions where a concrete finite representation is simpler.
- Do not use an existential theorem where the project already has an explicit bounding function available.
- Do not claim the final theorem is proved from asymptotic notation alone.
- Do not leave exploratory `#check`, `#print`, or `#eval` commands in final files unless they are intentionally in `Examples.lean`.
