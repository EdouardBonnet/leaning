import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic









namespace TwinWidth




structure TrigraphState (V : Type*) where
  

  bags : Finset (Finset V)
  
  bag_nonempty : ∀ ⦃A⦄, A ∈ bags → A.Nonempty
  
  bag_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B
  
  bag_cover : ∀ v : V, ∃ A ∈ bags, v ∈ A
  
  blackAdj : Finset V → Finset V → Prop
  
  redAdj : Finset V → Finset V → Prop
  
  black_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A
  
  red_symm : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A
  
  black_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A
  
  red_irrefl : ∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A
  
  black_red_disjoint : ∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B

namespace TrigraphState


noncomputable def singletonBags (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.image (fun v : V => ({v} : Finset V))

@[simp] theorem mem_singletonBags {V : Type*} [Fintype V] [DecidableEq V]
    {A : Finset V} :
    A ∈ singletonBags V ↔ ∃ v : V, A = {v} := by
  classical
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨v, _hv, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩

@[simp] theorem card_singletonBags (V : Type*) [Fintype V] [DecidableEq V] :
    (singletonBags V).card = Fintype.card V := by
  classical
  rw [singletonBags]
  refine Finset.card_image_of_injective _ ?_
  intro a b h
  exact Finset.singleton_inj.mp h


noncomputable def redDegree {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  by
    classical
    exact (T.bags.filter fun B => T.redAdj A B).card

end TrigraphState

end TwinWidth
