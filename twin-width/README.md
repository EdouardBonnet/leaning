# Twin-Width and Mixed Minor Number in Lean 4

This repository is a Lean 4/mathlib project whose main objective is to formalize the theorem that **twin-width** and **mixed minor number** are functionally equivalent graph parameters.

The intended mathematical target is the standard equivalence, for finite simple graphs, between bounded twin-width and bounded mixed minor number. Informally, if `tww(G)` is the twin-width of a graph and `mxn(G)` is the mixed minor number of its best ordered adjacency matrix, then there are functions bounding each parameter in terms of the other:

```text
mxn(G) ≤ F(tww(G))
tww(G) ≤ H(mxn(G))
```

A common quantitative form appearing in the literature is:

```text
(mxn(G) - 1) / 2 ≤ tww(G) ≤ 2^(2^O(mxn(G)))
```

The Lean development should aim first for a clean formal statement of functional equivalence, then progressively replace abstract bounding functions with explicit bounds as the formal proof matures.

## Mathematical scope

We work with finite simple undirected graphs. In mathlib, the base graph model is:

```lean
G : SimpleGraph V
```

where `V` is a finite vertex type. The project introduces the additional structures needed for twin-width and mixed minors rather than attempting to replace mathlib's graph library.

The central objects are:

1. **Ordered adjacency matrices** of finite simple graphs.
2. **Intervals and divisions** of finite linear orders.
3. **Mixed cells**, **mixed divisions**, and **mixed minors** of finite-alphabet matrices.
4. The **mixed minor number** of a matrix.
5. The **mixed minor number** of a graph, defined as the minimum matrix mixed minor number over all vertex orderings.
6. **Trigraphs** or red-edge graphs used to represent contraction sequences.
7. **Contraction sequences** and their maximum red degree.
8. The **twin-width** of a finite simple graph.
9. A formal notion of **functional equivalence** between graph parameters.
10. The theorem that twin-width and mixed minor number are functionally equivalent.

## Primary theorem

A recommended final-facing statement is:

```lean
def GraphParam := ∀ {V : Type*}, [Fintype V] → [DecidableEq V] → SimpleGraph V → ℕ

/-- Two graph parameters are functionally equivalent if each is bounded by
some numerical function of the other. -/
def FunctionallyEquivalent (p q : GraphParam) : Prop :=
  (∃ f : ℕ → ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    p G ≤ f (q G)) ∧
  (∃ g : ℕ → ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    q G ≤ g (p G))

/-- Twin-width and mixed minor number are functionally equivalent. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  -- proof
```

This exact signature may need adjustment as the project definitions mature. In particular, `GraphParam` may need explicit decidability assumptions for adjacency, or the project may choose `WithTop ℕ` if some minimization definitions are easier to stage that way. Prefer total `ℕ`-valued parameters for finite graphs when possible.

## Quantitative target statements

The project should decompose the main theorem into two directional results.

### Direction 1: twin-width bounds mixed minor number

Prove that bounded twin-width implies bounded mixed minor number. A concrete target is a linear bound of the form:

```lean
theorem mixedMinorNumber_le_of_twinWidth_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    mixedMinorNumber G ≤ 2 * twinWidth G + 2 := by
  -- proof
```

Depending on the chosen indexing convention, the constant may be `+1`, `+2`, or otherwise slightly different. Document the convention and prove a version consistent with the formal definitions.

### Direction 2: mixed minor number bounds twin-width

Prove that bounded mixed minor number implies bounded twin-width. Initially, use a named explicit bounding function:

```lean
/-- A concrete bound obtained from the mixed-minor-to-twin-width construction. -/
def twinWidthBoundOfMixedMinorNumber : ℕ → ℕ :=
  -- fill in once the formal quantitative proof is available

 theorem twinWidth_le_of_mixedMinorNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  -- proof
```

Do not encode asymptotic notation such as `2^(2^O(k))` as the final theorem. Either use an explicit elementary function, or state the qualitative result using existence of a bounding function.

## Repository layout

Use a layout that separates finite-order combinatorics, matrices, mixed minors, and contraction sequences:

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
lakefile.lean
lean-toolchain
README.md
AGENTS.md
```

The root module `TwinWidth.lean` should import only the public modules needed by downstream users:

```lean
import TwinWidth.Graph.MixedMinorNumber
import TwinWidth.Contraction.TwinWidth
import TwinWidth.Equivalence.Main
import TwinWidth.Examples
```

## Definition plan

### Ordered adjacency matrices

For a finite graph `G : SimpleGraph V` and an ordering/equivalence with `Fin n`, define a Boolean matrix:

```lean
adjMatrixOfOrder : SimpleGraph V → VertexOrder V n → Fin n → Fin n → Bool
```

The project may instead use `Matrix (Fin n) (Fin n) Bool` if this integrates better with mathlib. Keep the graph-ordering layer thin and reusable.

### Divisions

A `k`-division of `Fin n` should be a partition into `k` nonempty consecutive intervals. It should expose:

```lean
parts : Fin k → Finset (Fin n)
nonempty_part : ∀ i, (parts i).Nonempty
disjoint_parts : Pairwise (Disjoint on parts)
cover_parts : ⋃ i, parts i = Finset.univ
convex_parts : -- membership is interval-convex in the order
```

The exact representation may use cut points instead of sets. Cut points are often easier for consecutive intervals and cardinality proofs.

### Mixed cells and mixed minors

For a finite-alphabet matrix `M`, row division `R`, and column division `C`, define the cell at `(i,j)` and say it is mixed when it is neither vertical nor horizontal. For Boolean graph adjacency matrices, this specializes to the usual mixed-cell behavior.

```lean
def CellMixed (M : Matrix (Fin n) (Fin m) α)
    (R : Division n k) (C : Division m k) (i j : Fin k) : Prop :=
  ¬ CellVertical M R C i j ∧ ¬ CellHorizontal M R C i j
```

Then:

```lean
def HasMixedMinor (M : Matrix (Fin n) (Fin m) α) (k : ℕ) : Prop :=
  ∃ R : Division n k, ∃ C : Division m k,
    ∀ i j : Fin k, CellMixed M R C i j
```

Define matrix mixed number as the largest `k` for which `HasMixedMinor M k` holds. For finite matrices this can be defined via `Nat.findGreatest`, a finite supremum over `Finset.range`, or a maximum over possible `k ≤ min n m`.

### Graph mixed minor number

For a finite graph, define:

```lean
def mixedMinorNumber (G : SimpleGraph V) : ℕ :=
  -- minimum over all vertex orderings of the mixed number of the ordered adjacency matrix
```

The definition must be invariant under relabeling. A useful intermediate theorem is:

```lean
theorem mixedMinorNumber_eq_min_orderedAdjacencyMixedNumber ...
```

### Twin-width

Represent contraction sequences explicitly. A useful staged approach is:

1. Define trigraphs as a pair of black and red adjacency relations with invariants.
2. Define contraction of two vertices into one new vertex or, equivalently, contraction of parts of a partition of the original vertex set.
3. Define red degree.
4. Define a `d`-sequence as a full contraction sequence whose red degree never exceeds `d`.
5. Define `twinWidth G` as the least `d` admitting a `d`-sequence.

A partition-of-original-vertices representation is often more formalization-friendly than repeatedly changing vertex types.

## Milestones

### Milestone 0: project foundation

- Initialize the Lake project.
- Pin Lean and mathlib with `lean-toolchain` and `lake-manifest.json`.
- Add the module skeleton above.
- Confirm `lake build` succeeds with empty modules.

### Milestone 1: finite order and division infrastructure

- Define intervals or cut-point divisions of `Fin n`.
- Prove basic facts: nonemptiness, coverage, disjointness, monotonicity, refinement, and coarsening.
- Add tests/examples for small `n` and `k`.

### Milestone 2: Boolean matrix mixed minors

- Define cells, mixed cells, mixed divisions, and `HasMixedMinor`.
- Define matrix mixed number.
- Prove monotonicity lemmas in `k` where valid.
- Prove simple examples: constant matrices have mixed number `0` or no positive mixed minor, according to convention.

### Milestone 3: graph orderings and mixed minor number

- Define ordered adjacency matrices.
- Define graph mixed minor number as a minimum over orderings.
- Prove invariance under graph isomorphism/relabeling.
- Prove basic bounds such as `mixedMinorNumber G ≤ Fintype.card V`.

### Milestone 4: trigraphs and contraction sequences

- Define trigraph state and red degree.
- Define contraction on partition states.
- Define `HasTwinWidthAtMost G d`.
- Define `twinWidth G` and prove basic bounds for finite graphs.
- Prove examples: complete graphs and empty graphs have twin-width `0`; paths or small examples can be added later.

### Milestone 5: twin-width to mixed minors

- Formalize the ordered matrix extracted from a contraction sequence.
- Prove the linear mixed-minor bound from a bounded-width contraction sequence.
- Produce the first directional theorem:

```lean
mixedMinorNumber G ≤ 2 * twinWidth G + c
```

### Milestone 6: mixed minors to twin-width

- Formalize the construction that turns a mixed-minor-free ordered adjacency matrix into a bounded-width contraction sequence.
- Define the explicit bounding function.
- Prove:

```lean
twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G)
```

### Milestone 7: functional equivalence theorem

- Define graph-parameter functional equivalence.
- Combine the two directional theorems.
- Add documentation and examples.

## Contracts and Full Proofs

For large theorem families, the repository separates three kinds of files:

- `*Defs.lean`: definition-only modules containing predicates, structures, and
  explicit numerical bounds.
- `*Contract.lean`: front-end theorem modules exposing the intended
  natural-language statements in a compact form.
- full proof files, such as `Theorem10.lean`, where the supporting
  constructions and detailed lemmas are proved.

Contract files should not introduce new definitions or axioms.  Completed proof
files should not import a contract module to prove the corresponding theorem.
Contract theorem names should be theorem-style names, and their types should
state the mathematical claim directly.  Avoid contracts of the form
`theorem short_name : SomePredicateAlias someBound`; prefer explicit quantified
Lean statements such as `∀ M, MatrixTwinWidthAtMost M d →
matrixMixedNumber M ≤ 2 * d + 2`.
Each contract file should expose only the main final lemma for that proof
module.  Intermediate counting, greedy-step, ordered-matrix, or conversion
variants belong in proof files, not in the contract interface.

Current contract modules:

- `TwinWidth.Matrix.MarcusTardosContract` states the grid-minor density theorem.
- `TwinWidth.Matrix.DivisionSequenceContract` states Lemma 13 in full
  bounded-division-sequence form.
- `TwinWidth.Matrix.Theorem10Contract` states the final two-direction matrix
  Theorem 10 interface.
- `TwinWidth.Equivalence.TwinWidthToMixedContract` states the reduction from an
  ordered-adjacency linear bound to the graph linear bound.
- `TwinWidth.Graph.Theorem14Contract` states the graph Theorem 14 bridge from
  the mirrored symmetric matrix construction to the graph twin-width bound.
- `TwinWidth.Equivalence.MixedToTwinWidthContract` states the reduction from an
  ordered-adjacency Theorem 10 bound to the graph mixed-minor bound.
- `TwinWidth.Equivalence.MainContract` states the combiner from the two
  explicit directional bounds to functional equivalence.

Current matrix Theorem 10 status:

- `TwinWidth.Matrix.Theorem10Defs` contains the statement-level definitions and
  explicit bounds.
- `TwinWidth.Matrix.Theorem10Contract` exposes the full two-direction matrix
  Theorem 10 interface as theorem wrappers.
- `TwinWidth.Matrix.Theorem10` proves the ordered first item and the second
  item, then packages them as the full two-direction matrix Theorem 10
  interface.  The first item uses `MatrixTwinOrderedAtMost`, matching the
  ordered-matrix hypothesis in the paper.

Current graph equivalence status:

- `TwinWidth.Graph.Theorem14` proves the graph interpretation of symmetric
  matrix contraction sequences.  The remaining Theorem 14 input is the
  mirrored symmetric matrix construction for mixed-free square Boolean
  matrices.
- `TwinWidth.Graph.TwinDecomposition` records the leaf-order interface for the
  twin-width-to-mixed-minor direction.  The remaining input is the construction
  of that leaf order from a width-`twinWidth G` contraction tree.
- `TwinWidth.Equivalence.Main` combines these two explicit inputs into
  functional equivalence without using axioms.

## Lean and mathlib conventions

Use mathlib definitions whenever possible. Do not define a parallel simple graph library.

Expected imports include:

```lean
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Nat
```

Additional imports should be added only when needed.

Use namespaces consistently:

```lean
namespace TwinWidth

namespace Matrix
-- matrix definitions
end Matrix

namespace SimpleGraph
-- graph-parameter definitions about `SimpleGraph`
end SimpleGraph

end TwinWidth
```

Suggested theorem names:

```lean
hasMixedMinor_mono
not_hasMixedMinor_constant
mixedNumber_le_min_card
mixedMinorNumber_le_card
hasTwinWidthAtMost_iff_exists_contractionSequence
twinWidth_le_of_hasTwinWidthAtMost
mixedMinorNumber_le_of_twinWidth_le
twinWidth_le_of_mixedMinorNumber
twinWidth_functionallyEquivalent_mixedMinorNumber
```

## Verification commands

After dependency setup:

```bash
lake exe cache get
lake build
```

To check a single file:

```bash
lake env lean TwinWidth/Matrix/MixedMinor.lean
```

Before handing off completed Lean code:

```bash
lake build
grep -R --line-number --include='*.lean' -E '\bsorry\b|\badmit\b|\baxiom\b|unsafe' TwinWidth
```

The grep command should produce no matches.

## Non-goals

- Do not formalize general graph theory unrelated to twin-width unless it is needed for the main theorem.
- Do not introduce multigraphs, directed graphs, or arbitrary relational structures in the first pass.
- Do not use asymptotic notation as a final Lean statement.
- Do not hide unproved mathematics behind axioms.
- Do not redefine mathlib concepts such as `SimpleGraph`, `Fintype`, `Matrix`, `Finset`, or graph isomorphism.

## References for contributors

- Édouard Bonnet, Eun Jung Kim, Stéphan Thomassé, Rémi Watrigant, twin-width papers introducing the mixed-minor characterization.
- Édouard Bonnet, Colin Geniet, Eun Jung Kim, Stéphan Thomassé, Rémi Watrigant, *Twin-width II: small classes*.
- Édouard Bonnet and Hugues Déprés, *Twin-width can be exponential in treewidth*.
- mathlib `SimpleGraph` documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html
- OpenAI Codex `AGENTS.md` guide: https://developers.openai.com/codex/guides/agents-md
