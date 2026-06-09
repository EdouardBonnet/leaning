import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.4.1.
Natural-language statement:
The vertices of a finite connected graph can be enumerated so that every
initial induced subgraph is connected.
-/
axiom proposition_1_4_1 {V : Type u} (G : SimpleGraph V) [Fintype V] :
  G.Connected →
    ∃ A : ℕ → Set V,
      A 0 = ∅ ∧
        A (Fintype.card V) = Set.univ ∧
          ∀ i : ℕ, i < Fintype.card V →
            A i ⊆ A (i + 1) ∧
              (A (i + 1)).ncard = i + 1 ∧
                (G.induce (A (i + 1))).Connected

end Chapter01
end Diestel
