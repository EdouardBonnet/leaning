import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v w

/--
Diestel, Proposition 1.7.1.
Natural-language statement:
The minor relation and topological-minor relation are partial orders on
finite graphs, up to graph isomorphism.
-/
axiom proposition_1_7_1 :
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
                IsTopologicalMinor X Y → IsTopologicalMinor Y X → Nonempty (X ≃g Y))

end Chapter01
end Diestel
