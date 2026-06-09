import Chapter01.proposition_1_7_1_support
import Chapter01.topological_compose_walk

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v w

/--
Diestel, Proposition 1.7.1.
Natural-language statement:
The minor relation and topological-minor relation are partial orderings on
the class of finite graphs, up to graph isomorphism.
-/
theorem proposition_1_7_1 :
  (∀ {V : Type u} (X : SimpleGraph V), IsMinor X X) ∧
    (∀ {V : Type u} {W : Type v} {U : Type w}
      (X : SimpleGraph V) (Y : SimpleGraph W) (Z : SimpleGraph U),
        IsMinor X Y → IsMinor Y Z → IsMinor X Z) ∧
      (∀ {V : Type u} {W : Type v} (X : SimpleGraph V) (Y : SimpleGraph W),
        Finite V → Finite W → IsMinor X Y → IsMinor Y X → Nonempty (X ≃g Y)) ∧
        (∀ {V : Type u} (X : SimpleGraph V), IsTopologicalMinor X X) ∧
          (∀ {V : Type u} {W : Type v} {U : Type w}
            (X : SimpleGraph V) (Y : SimpleGraph W) (Z : SimpleGraph U),
              IsTopologicalMinor X Y → IsTopologicalMinor Y Z → IsTopologicalMinor X Z) ∧
            (∀ {V : Type u} {W : Type v} (X : SimpleGraph V) (Y : SimpleGraph W),
              Finite V → Finite W →
                IsTopologicalMinor X Y → IsTopologicalMinor Y X → Nonempty (X ≃g Y)) := by
  rcases proposition_1_7_1_without_topological_trans with
    ⟨hminor_refl, hminor_trans, hminor_antisymm, htop_refl, htop_antisymm⟩
  exact
    ⟨hminor_refl, hminor_trans, hminor_antisymm, htop_refl,
      (fun X Y Z => isTopologicalMinor_trans X Y Z), htop_antisymm⟩

end Chapter01
end Diestel
