import Chapter01.normal_tree

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Lemma 1.5.4.
Normal trees reflect separation: incomparable vertices are separated by
the intersection of their down-closures, and down-closed deletions have
components spanned by the up-closures of minimal remaining vertices.
-/
theorem lemma_1_5_4 {V : Type u} (G T : SimpleGraph V) (r : V) :
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
                      C = up_closure T r x) := by
  intro hnormal
  constructor
  · exact normal_vertexSetSeparates_incomparable hnormal
  · intro S C hS hC_sub hC_conn hC_max
    by_cases hrS : r ∈ S
    · exact normal_component_nonroot_case hnormal hS hrS hC_sub hC_conn hC_max
    · exact ⟨r, normal_component_root_case hnormal hS hrS hC_sub hC_conn hC_max⟩

end Chapter01
end Diestel
