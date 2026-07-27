import «statements-and-proofs».ChekuriChuzhoyTheorem215Contract
import «statements-and-proofs».ChekuriChuzhoyTheoremB1Contract
import «statements-and-proofs».ChekuriChuzhoyStitchedRows

/-!
# Contract for Chekuri--Chuzhoy Theorem 3.1

Theorem 3.1 is the local routing theorem used inside each even cluster of a
path-of-sets system.  The statement below is localized to a finite connected
vertex set `C`: linkedness is stated inside `C`, and the paths and bridges
returned by the theorem are required to stay inside `C`.  This is the form
directly applied to induced cluster subgraphs.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyContract

universe u

/-- Chekuri--Chuzhoy Theorem 3.1, structural localized form.

For linked equal-size terminal sets `A` and `B` in a connected region `C`, with
`(16 * h + 10) * q <= w`, either the ambient graph contains an `h x h` grid
minor, or there are `q` disjoint `A`-to-`B` paths inside `C` and every pair of
these paths has a bridge inside `C` internally disjoint from the path family. -/
axiom theorem31_gridMinor_or_linked_paths :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
        1 < h →
          1 < q →
            IsCluster G C →
              NodeLinkedIn G C A B →
                A.card = w →
                  B.card = w →
                    (16 * h + 10) * q ≤ w →
                      ContainsGridMinor G h ∨
                        ∃ P : PathPacking G A B,
                          P.card = q ∧ P.StaysIn C ∧ P.HasPairwiseBridgesIn C

/-- The contract theorem supplies the faithful local-routing input used by the
Corollary 3.2 formalization. -/
theorem localRoutingClusterInput_of_theorem31_contract :
    ChekuriChuzhoy.LocalRoutingClusterInput.{u} := by
  intro V _ _ G C A B h q w hh hq hcluster hlinked hA hB hwidth
  exact theorem31_gridMinor_or_linked_paths
    G hh hq hcluster hlinked hA hB hwidth

end ChekuriChuzhoyContract
end SimpleGraph
