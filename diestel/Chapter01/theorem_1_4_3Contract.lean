import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.4.3 (Mader).
Natural-language statement:
If `k ≠ 0` and `d(G) > 4k`, then `G` has a `(k+1)`-connected subgraph
`H` such that `d(H) > d(G) - 2k > 2k`.
-/
axiom theorem_1_4_3 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (k : ℕ) :
  k ≠ 0 →
    (4 * k : ℚ) < average_degree G →
      ∃ U : Set V,
        letI : Fintype U := Fintype.ofFinite U
        letI : DecidableRel (G.induce U).Adj := Classical.decRel (G.induce U).Adj
        IsKConnected (G.induce U) (k + 1) ∧
          average_degree (G.induce U) > average_degree G - (2 * k : ℚ) ∧
            (2 * k : ℚ) < average_degree G - (2 * k : ℚ)

end Chapter01
end Diestel
