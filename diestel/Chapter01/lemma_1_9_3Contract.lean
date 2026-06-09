import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Lemma 1.9.3.
Natural-language statement:
Every cut is a disjoint union of bonds.
-/
axiom lemma_1_9_3 {V : Type u} (G : SimpleGraph V) [Fintype V] (F : Set G.edgeSet) :
  IsCut G F →
    ∃ bonds : Set (Set G.edgeSet),
      (∀ B ∈ bonds, IsBond G B) ∧
        (∀ B₁ ∈ bonds, ∀ B₂ ∈ bonds, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
          F = {e | ∃ B ∈ bonds, e ∈ B}

end Chapter01
end Diestel
