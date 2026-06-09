import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Theorem 2.4.4 (Bowler-Carmesin).
Natural-language statement:
For every connected graph and every `k`, there is a partition whose
induced parts have `k` edge-disjoint spanning trees and whose quotient
has its crossing edges covered by `k` spanning trees.
-/
axiom theorem_2_4_4 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.Loopless G →
    MultiGraph.Connected G →
      ∃ P : Finset (Set V), MultiGraph.PackingCoveringPartition G P k

end Chapter02
end Diestel
