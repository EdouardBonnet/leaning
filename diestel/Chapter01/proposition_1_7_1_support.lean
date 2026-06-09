import Chapter01.minor_equal_vertices
import Chapter01.topological_finite

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v w

theorem proposition_1_7_1_without_topological_trans :
  (∀ {V : Type u} (X : SimpleGraph V), IsMinor X X) ∧
    (∀ {V : Type u} {W : Type v} {U : Type w}
      (X : SimpleGraph V) (Y : SimpleGraph W) (Z : SimpleGraph U),
        IsMinor X Y → IsMinor Y Z → IsMinor X Z) ∧
      (∀ {V : Type u} {W : Type v} (X : SimpleGraph V) (Y : SimpleGraph W),
        Finite V → Finite W → IsMinor X Y → IsMinor Y X → Nonempty (X ≃g Y)) ∧
        (∀ {V : Type u} (X : SimpleGraph V), IsTopologicalMinor X X) ∧
          (∀ {V : Type u} {W : Type v} (X : SimpleGraph V) (Y : SimpleGraph W),
              Finite V → Finite W →
                IsTopologicalMinor X Y → IsTopologicalMinor Y X → Nonempty (X ≃g Y)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V X
    exact isMinor_refl X
  · intro V W U X Y Z
    exact isMinor_trans X Y Z
  · intro V W X Y hV hW
    letI : Finite V := hV
    letI : Finite W := hW
    exact isMinor_antisymm_iso X Y
  · intro V X
    exact isTopologicalMinor_refl X
  · intro V W X Y hV hW
    letI : Finite V := hV
    letI : Finite W := hW
    exact isTopologicalMinor_antisymm_iso X Y

end Chapter01
end Diestel
