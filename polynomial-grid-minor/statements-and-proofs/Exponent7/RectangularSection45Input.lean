import «statements-and-proofs».Exponent7.RectangularTheorem415

/-!
# Rectangular Section 4.5 input and assembly

The existing `Section45.Section45Input` specializes the selected chain length
and connector width to one number `w`.  The exponent-seven route needs a
strong path-of-sets system that is short and wide, so these parameters must be
independent.

This module keeps the proved graph assembly object
`Section45.WeakPathOfSetsAssemblyData G L W` unchanged.  Only the finite
selection input is generalized:

* `L` is the requested number of selected clusters;
* `W` is the consecutive-overlap threshold and the width of every nail and
  connector family.

No paper theorem is assumed here.  A later producer must construct the
`assembly` field from the parent-ordered happy-cluster table.
-/

namespace SimpleGraph
namespace Exponent7

universe u

open Finset

variable {V : Type u} [DecidableEq V]

/-- Proof-facing input for rectangular Chuzhoy--Tan Section 4.5.

Unlike `Section45.Section45Input`, the selected length `L` and width `W` are
independent.  The assembly field contains exactly the concrete cluster, nail,
connector, disjointness, and weak-well-linkedness data consumed by the
existing axiom-free graph constructor. -/
structure RectangularSection45Input
    (G : _root_.SimpleGraph V) (N M D L W : ℕ) where
  sliceRows : Fin M → Finset (Fin N)
  length_pos : 0 < L
  width_pos : 0 < W
  N_large : 3 * W ≤ N
  D_square : 4 * N * W ≤ D ^ 2
  large : 2 * N * L ≤ D * M
  row_card : ∀ i : Fin M, D ≤ (sliceRows i).card
  assembly :
    ∀ (l : List (Fin M)) (hlen : l.length = L),
      l.IsChain (Section45.LargeOverlapRel sliceRows W) →
        Section45.WeakPathOfSetsAssemblyData G L W

/-- Rectangular Section 4.5 is an immediate composition of the rectangular
finite selection theorem and the already-proved graph assembly theorem. -/
theorem rectangular_section45_weak_pathOfSetsSystem
    {G : _root_.SimpleGraph V} {N M D L W : ℕ}
    (Input : RectangularSection45Input G N M D L W) :
    Nonempty (WeakPathOfSetsSystem G L W) := by
  rcases theorem415_rectangular Input.sliceRows Input.width_pos
      Input.N_large Input.D_square Input.large Input.row_card with
    ⟨l, hlen, hchain⟩
  exact Section45.weak_pathOfSetsSystem_of_section45_assembly
    (Input.assembly l hlen hchain)

/-- The proposition exposed to later exponent-seven composition modules. -/
def RectangularSection45Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {N M D L W : ℕ},
      RectangularSection45Input G N M D L W →
        Nonempty (WeakPathOfSetsSystem G L W)

theorem rectangularSection45Statement :
    RectangularSection45Statement.{u} := by
  intro V _ G N M D L W Input
  exact rectangular_section45_weak_pathOfSetsSystem Input

end Exponent7
end SimpleGraph
