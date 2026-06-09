import Chapter01.finite_hom_iso

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

private noncomputable def modelVertexMap {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} (M : Model X Y) : A ↪ B where
  toFun := fun x => Classical.choose (M.nonempty x)
  inj' := by
    intro x y hxy
    have hx : Classical.choose (M.nonempty x) ∈ M.branchSet x :=
      Classical.choose_spec (M.nonempty x)
    have hy : Classical.choose (M.nonempty y) ∈ M.branchSet y :=
      Classical.choose_spec (M.nonempty y)
    by_contra hne
    have hdisj := M.pairwise_disjoint hne
    change Disjoint (M.branchSet x) (M.branchSet y) at hdisj
    rw [Set.disjoint_left] at hdisj
    exact hdisj hx (by simpa [hxy] using hy)

private lemma modelVertexMap_mem {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} (M : Model X Y) (x : A) :
    modelVertexMap M x ∈ M.branchSet x :=
  Classical.choose_spec (M.nonempty x)

private lemma model_branch_singleton_of_card_eq {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} [Finite A] [Finite B]
    (M : Model X Y) (hcard : Nat.card A = Nat.card B) (x : A) :
    M.branchSet x = {modelVertexMap M x} := by
  classical
  let f := modelVertexMap M
  have hbij : Function.Bijective f := by
    letI : Fintype A := Fintype.ofFinite A
    letI : Fintype B := Fintype.ofFinite B
    have hcardF : Fintype.card A = Fintype.card B := by
      simpa [Nat.card_eq_fintype_card] using hcard
    exact (Fintype.bijective_iff_injective_and_card (f : A → B)).mpr
      ⟨f.injective, hcardF⟩
  ext z
  constructor
  · intro hz
    obtain ⟨x', hx'⟩ := hbij.2 z
    have hz' : f x' ∈ M.branchSet x := by
      simpa [hx'] using hz
    by_cases hxx' : x = x'
    · subst x'
      rw [← hx']
      exact Set.mem_singleton (f x)
    · have hdisj := M.pairwise_disjoint hxx'
      change Disjoint (M.branchSet x) (M.branchSet x') at hdisj
      rw [Set.disjoint_left] at hdisj
      exact False.elim (hdisj hz' (modelVertexMap_mem M x'))
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact modelVertexMap_mem M x

theorem modelVertexMap_bijective_of_card_eq {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} [Finite A] [Finite B]
    (M : Model X Y) (hcard : Nat.card A = Nat.card B) :
    Function.Bijective (modelVertexMap M) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have hcardF : Fintype.card A = Fintype.card B := by
    simpa [Nat.card_eq_fintype_card] using hcard
  exact (Fintype.bijective_iff_injective_and_card (modelVertexMap M : A → B)).mpr
    ⟨(modelVertexMap M).injective, hcardF⟩

theorem modelVertexMap_adj_of_card_eq {A : Type u} {B : Type v}
    {X : SimpleGraph A} {Y : SimpleGraph B} [Finite A] [Finite B]
    (M : Model X Y) (hcard : Nat.card A = Nat.card B)
    {x y : A} (hxy : X.Adj x y) :
    Y.Adj (modelVertexMap M x) (modelVertexMap M y) := by
  obtain ⟨a, ha, b, hb, hab⟩ := M.adjacent hxy
  have hx := model_branch_singleton_of_card_eq M hcard x
  have hy := model_branch_singleton_of_card_eq M hcard y
  have ha' : a = modelVertexMap M x := by
    rw [hx, Set.mem_singleton_iff] at ha
    exact ha
  have hb' : b = modelVertexMap M y := by
    rw [hy, Set.mem_singleton_iff] at hb
    exact hb
  simpa [ha', hb'] using hab

theorem isMinor_antisymm_iso {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B] :
    IsMinor X Y → IsMinor Y X → Nonempty (X ≃g Y) := by
  intro hXY hYX
  rcases hXY with ⟨MXY⟩
  rcases hYX with ⟨MYX⟩
  have hcardXY := isMinor_card_le X Y ⟨MXY⟩
  have hcardYX := isMinor_card_le Y X ⟨MYX⟩
  have hcard : Nat.card A = Nat.card B := le_antisymm hcardXY hcardYX
  exact graph_iso_of_bijective_homs X Y (modelVertexMap MXY) (modelVertexMap MYX)
    (modelVertexMap_bijective_of_card_eq MXY hcard)
    (modelVertexMap_bijective_of_card_eq MYX hcard.symm)
    (fun h => modelVertexMap_adj_of_card_eq MXY hcard h)
    (fun h => modelVertexMap_adj_of_card_eq MYX hcard.symm h)

end Chapter01
end Diestel
