import Chapter01.definitions_ch1
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.9.5.
Natural-language statement:
For a connected graph with spanning tree `T`, the fundamental cuts and
fundamental cycles with respect to `T` form bases of the cut and cycle
spaces. Consequently, `dim B(G) = n - 1` and `dim C(G) = m - n + 1`.
The last expression is formalized as `m + 1 - n`, since Lean's `Nat`
subtraction is truncated.
-/
axiom theorem_1_9_5 {V : Type u} (G T : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet] :
  G.Connected →
    IsSpanningTree G T →
      (∀ e : Sym2 V, e ∈ G.edgeSet → e ∉ T.edgeSet →
        ∃ a : V, ∃ c : G.Walk a a, IsFundamentalCycle G T e c) ∧
        (∀ f : G.edgeSet, (f : Sym2 V) ∈ T.edgeSet →
          ∃ D : Set G.edgeSet,
            IsBond G D ∧ f ∈ D ∧
              ∀ e : G.edgeSet, e ∈ D → e = f ∨ (e : Sym2 V) ∉ T.edgeSet) ∧
          Module.finrank (ZMod 2) (cut_space G) = Fintype.card V - 1 ∧
            Module.finrank (ZMod 2) (cycle_space G) =
              G.edgeFinset.card + 1 - Fintype.card V

end Chapter01
end Diestel
