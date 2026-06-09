import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.2.2.
Natural-language statement:
Every graph with at least one edge has an induced subgraph `H` with
`δ(H) > ε(H) ≥ ε(G)`.
-/
axiom proposition_1_2_2 {V : Type u} (G : SimpleGraph V) [Finite V] :
  0 < Nat.card G.edgeSet →
    ∃ U : Set V, U.Nonempty ∧
      (let H := G.induce U
       ((Nat.card G.edgeSet : ℚ) / Nat.card V ≤
          (Nat.card H.edgeSet : ℚ) / Nat.card U) ∧
        ∀ v : U,
          (Nat.card H.edgeSet : ℚ) / Nat.card U <
            (Nat.card (H.neighborSet v) : ℚ))

end Chapter01
end Diestel
