import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Corollary 2.2.2 (Petersen).
Natural-language statement:
Every finite bridgeless cubic graph has a 1-factor.
-/
axiom corollary_2_2_2 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  IsCubic G →
    IsBridgeless G →
      ∃ M : G.Subgraph, M.IsPerfectMatching

end Chapter02
end Diestel
