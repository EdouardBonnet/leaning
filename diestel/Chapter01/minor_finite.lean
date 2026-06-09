import Chapter01.minor_transitive

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

theorem isMinor_card_le {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B] :
    IsMinor X Y → Nat.card A ≤ Nat.card B := by
  intro hminor
  classical
  rcases hminor with ⟨M⟩
  let f : A → B := fun x => Classical.choose (M.nonempty x)
  have hf_mem : ∀ x : A, f x ∈ M.branchSet x := by
    intro x
    exact Classical.choose_spec (M.nonempty x)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hdisj := M.pairwise_disjoint hne
    change Disjoint (M.branchSet x) (M.branchSet y) at hdisj
    rw [Set.disjoint_left] at hdisj
    exact hdisj (hf_mem x) (by simpa [f, hxy] using hf_mem y)
  exact Nat.card_le_card_of_injective f hf_inj

theorem isTopologicalMinor_card_le {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B] :
    IsTopologicalMinor X Y → Nat.card A ≤ Nat.card B := by
  rintro ⟨M⟩
  exact Nat.card_le_card_of_injective M.vertexMap M.vertexMap.injective

end Chapter01
end Diestel
