# AGENTS.md — Diestel Lean Formalization

## Goal

Formalize Diestel's graph theory proofs in Lean 4, chapter by chapter, using Mathlib's `SimpleGraph` library. Each chapter folder contains its own PDF, e.g.

```text
Chapter01/ch1.pdf
Chapter02/ch2.pdf
Chapter03/ch3.pdf
```

Use the PDF in the chapter folder as the source for that chapter.

---

## Core rules

Use Mathlib graph definitions whenever they exist. Do **not** redefine notions already in Mathlib.

Main graph representation:

```lean
SimpleGraph V
```

Prefer Mathlib imports such as:

```lean
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
```

Before defining anything, search the local Mathlib checkout for an existing definition or theorem.

Use only the imports needed by the file. Do not use `import Mathlib` as a default; if a broad
import is unavoidable, document why in `inventory.md`.

---

## What to formalize

For each chapter, formalize:

1. All genuine definitions not already in Mathlib.
2. All numbered results: theorems, propositions, lemmas, corollaries.
3. Any unnumbered results only if they are used as proof ingredients.

Ignore:

- examples,
- exercises,
- informal remarks,
- notation-only paragraphs,
- notation that is not a mathematical definition,
- motivational text.

If a notation paragraph introduces a real concept not already in Mathlib, formalize the concept, not the notation.

---

## File names

Use underscores only.

Examples:

```text
Chapter03/definitions_ch3.lean
Chapter03/theorem_3_1_4Contract.lean
Chapter03/theorem_3_1_4.lean
Chapter03/lemma_3_2_1Contract.lean
Chapter03/lemma_3_2_1.lean
```

Do not use hyphens in Lean filenames.

Declaration names also use underscores:

```lean
theorem_3_1_4
lemma_3_2_1
corollary_4_1_7
definition_2_3_5
```

Use namespaces:

```lean
namespace Diestel
namespace Chapter03

-- declarations

end Chapter03
end Diestel
```

---

## Chapter workflow

For chapter `N`, do the following in order.

### Review checkpoints

For every chapter, work in three review phases:

1. Complete the inventory and definition file first, then stop and ask the user to check them.
2. After the user approves the definitions, create the contract files, then stop and ask the user to check them.
3. After the user approves the contracts, work autonomously on the self-contained proof files until the chapter completion criterion is met.

### 1. Inventory

Create:

```text
ChapterNN/inventory.md
```

List:

- genuine definitions in the chapter,
- whether each is already in Mathlib,
- new definitions needed,
- all numbered statements,
- dependencies between statements,
- statements to ignore because they are examples, exercises, remarks, or notation-only.

### 2. Definitions

Create:

```text
ChapterNN/definitions_chN.lean
```

This file contains imports, namespaces, missing definitions, and small API lemmas.

Rules:

- Use existing Mathlib definitions whenever possible.
- Add a local abbreviation only if it improves readability.
- Do not duplicate Mathlib concepts under new definitions.
- Keep definitions honest; do not hide theorem content inside structures or predicates.
- Add `[Finite V]`, `[Fintype V]`, `[DecidableEq V]`, or `[DecidableRel G.Adj]` only when needed.
- Definition files must not contain `simp`, `simpa`, `simp_all`, `simp_rw`, or similar
  simplifier-driven proof blocks inside definitions. If a definition creates proof obligations,
  either state the underlying set/function directly or move the API/proof obligations to lemmas.

Example:

```lean
/--
Diestel, Chapter 3.
A vertex set `S` separates `A` from `B` in `G`.
Use this only if Mathlib has no suitable separator definition.
-/
def Separates (G : SimpleGraph V) (S A B : Set V) : Prop := ...
```

### 3. Contract files

For each numbered statement, create one contract file:

```text
ChapterNN/theorem_N_X_YContract.lean
```

A contract file contains the intended Lean statement as an `axiom`.

Example:

```lean
import Diestel.Chapter03.definitions_ch3

set_option linter.all false

namespace Diestel
namespace Chapter03

/--
Diestel, Theorem 3.1.4.
Natural-language statement:
...
-/
axiom theorem_3_1_4 :
  -- Lean statement
  True

end Chapter03
end Diestel
```

Contract files are for statement validation. They may contain `axiom`; other files may not.

Do not put more than one main statement in a contract file.

### 4. Proof files

After definitions and contracts are validated, create one proof file per contract:

```text
ChapterNN/theorem_N_X_Y.lean
```

The proof file must:

- import definitions and earlier finalized proof files as needed,
- not import its own contract file,
- restate exactly the same theorem as the contract,
- prove it without `sorry`, `admit`, `axiom`, `constant`, `opaque`, or `unsafe`.

Example:

```lean
import Diestel.Chapter03.definitions_ch3
import Diestel.Chapter03.theorem_3_1_3

set_option linter.all false

namespace Diestel
namespace Chapter03

theorem theorem_3_1_4 :
  -- same statement as theorem_3_1_4Contract.lean
  ... := by
  ...

end Chapter03
end Diestel
```

---

## Contract discipline

Only files ending in `Contract.lean` may contain `axiom`.

Final proof files must never import contract files.

After proving a statement, check that the proof does not depend on the contract:

```lean
#print axioms Diestel.Chapter03.theorem_3_1_4
```

The output must not contain any project-specific contract axiom.

A chapter aggregate file must import only definitions and finalized proof files, never contracts.

Example:

```lean
import Diestel.Chapter03.definitions_ch3
import Diestel.Chapter03.theorem_3_1_1
import Diestel.Chapter03.theorem_3_1_2
import Diestel.Chapter03.theorem_3_1_3
import Diestel.Chapter03.theorem_3_1_4
```

---

## PDF use

Each chapter folder contains its chapter PDF, for example:

```text
Chapter03/ch3.pdf
```

Use that file only for the relevant chapter.

Helpful commands:

```bash
pdftotext -layout ch3.pdf -
pdftotext -f 10 -l 20 -layout ch3.pdf /tmp/ch3_pages_10_20.txt
```

If extraction is ambiguous, inspect the PDF page manually. Do not guess statements from bad extraction.

---

## Statement style

Prefer general vertex types:

```lean
variable {V : Type u}
variable (G : SimpleGraph V)
```

Use `Set V` for arbitrary vertex sets. Use `Finset V` only when finite enumeration or cardinality is needed.

Make implicit assumptions explicit:

- finite graph,
- nonempty graph,
- connected graph,
- disjoint sets,
- induced subgraph versus arbitrary subgraph,
- vertex-disjoint versus internally disjoint paths,
- whether path endpoints may lie in a separator.

Check Diestel's conventions carefully against Mathlib's conventions.

Preserve strict and non-strict inequalities exactly. PDF text extraction can render symbols
such as `≤`, `≥`, `<`, and `>` ambiguously; if an inequality is central to a statement or proof,
verify it against the mathematical context or inspect the PDF manually before writing the contract.

---

## Proof style

Follow the mathematical structure of Diestel's proof, but split it into small Lean lemmas.

Use `classical` locally when helpful.

Proof files may include:

```lean
set_option linter.all false
```

This suppresses style noise only. It does not permit axioms, `sorry`, or hidden assumptions.

When blocked, add a note to `inventory.md` describing the missing lemma or definition. Do not add an axiom outside a contract file.

---

## Completion criterion

A chapter is complete when:

1. `definitions_chN.lean` compiles.
2. Every numbered statement has a contract file.
3. Every contract has a corresponding proof file.
4. No proof file imports a contract file.
5. No proof file contains `sorry`, `admit`, `axiom`, `constant`, `opaque`, or `unsafe`.
6. `#print axioms` for each finalized theorem reports no project-specific contract axiom.
7. The chapter aggregate file compiles without importing contracts.
