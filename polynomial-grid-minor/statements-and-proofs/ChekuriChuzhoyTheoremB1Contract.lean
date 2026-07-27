import «statements-and-proofs».ChekuriChuzhoyStructural

/-!
# Contract for Chekuri--Chuzhoy Theorem B.1

This is the non-algorithmic rerouting lemma used in the proof of Theorem 3.1.
In the paper this lemma is applied inside the Theorem 3.1 setup: the ambient
graph is connected and the terminal sets `A` and `B` are linked.  The linkedness
hypothesis is essential in Appendix B.1, where the proof constructs disjoint
paths from the `A`-endpoints of one block of linkage paths to the `B`-endpoints
of another block.
-/

namespace SimpleGraph
namespace ChekuriChuzhoyContract

universe u

/-- Chekuri--Chuzhoy Theorem B.1, structural form.

For linked disjoint terminal sets in a connected finite graph, every bad
`A`-`B` linkage either already yields an `h x h` grid minor, or can be rerouted
to an `A`-`B` linkage whose auxiliary graph has strictly fewer degree-two
vertices. -/
axiom theoremB1_gridMinor_or_rerouted_linkage :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V) {A B : Finset V} {h : ℕ}
      (L : PerfectPathPacking G A B),
        G.Connected →
          NodeLinkedIn G Finset.univ A B →
            1 < h →
              ¬ ChekuriChuzhoy.GoodLinkage L h →
                ContainsGridMinor G h ∨
                  ∃ L' : PerfectPathPacking G A B,
                    ChekuriChuzhoy.linkageAuxDegreeTwoCount L' <
                      ChekuriChuzhoy.linkageAuxDegreeTwoCount L

end ChekuriChuzhoyContract
end SimpleGraph
