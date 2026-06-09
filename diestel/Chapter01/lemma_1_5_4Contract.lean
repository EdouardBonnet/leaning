import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Lemma 1.5.4.
Natural-language statement:
Normal trees reflect separation: incomparable vertices are separated by
the intersection of their down-closures, and down-closed deletions have
components spanned by the up-closures of minimal remaining vertices.
-/
axiom lemma_1_5_4 {V : Type u} (G T : SimpleGraph V) (r : V) :
  IsNormalSpanningTree G T r →
    (∀ x y : V,
      ¬ TreeComparable T r x y →
        SeparatesVertices G (down_closure T r x ∩ down_closure T r y) x y) ∧
      (∀ S C : Set V,
        (∀ x ∈ S, down_closure T r x ⊆ S) →
          C ⊆ Sᶜ →
            (G.induce C).Connected →
              (∀ D : Set V, C ⊂ D → D ⊆ Sᶜ → ¬ (G.induce D).Connected) →
                ∃ x : V,
                  x ∉ S ∧
                    (∀ y : V, y ∉ S → TreeOrder T r y x → y = x) ∧
                      C = up_closure T r x)

end Chapter01
end Diestel
