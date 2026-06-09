import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Corollary 2.1.5 (Petersen).
Natural-language statement:
Every finite regular graph of positive even degree has a 2-factor.
-/
axiom corollary_2_1_5 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (k : ℕ) :
  1 ≤ k →
    G.IsRegularOfDegree (2 * k) →
      HasKFactor G 2

end Chapter02
end Diestel
