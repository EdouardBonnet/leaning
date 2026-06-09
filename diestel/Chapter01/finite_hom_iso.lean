import Chapter01.minor_finite

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

private noncomputable def edgeMapOfInjectiveHom {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) (f : A ↪ B)
    (hfadj : ∀ {x y : A}, X.Adj x y → Y.Adj (f x) (f y)) :
    X.edgeSet → Y.edgeSet := by
  intro e
  rcases e with ⟨se, hse⟩
  refine ⟨f.sym2Map se, ?_⟩
  rw [Function.Embedding.sym2Map_apply]
  induction se using Sym2.inductionOn with
  | hf x y =>
      rw [Sym2.map_mk]
      exact (SimpleGraph.mem_edgeSet Y).mpr
        (hfadj ((SimpleGraph.mem_edgeSet X).mp hse))

private lemma edgeMapOfInjectiveHom_injective {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) (f : A ↪ B)
    (hfadj : ∀ {x y : A}, X.Adj x y → Y.Adj (f x) (f y)) :
    Function.Injective (edgeMapOfInjectiveHom X Y f hfadj) := by
  intro e e' h
  apply Subtype.ext
  have hval := congrArg (fun e : Y.edgeSet => (e : Sym2 B)) h
  change f.sym2Map (e : Sym2 A) = f.sym2Map (e' : Sym2 A) at hval
  exact f.sym2Map.injective hval

private theorem edge_card_le_of_injective_hom {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B]
    (f : A ↪ B)
    (hfadj : ∀ {x y : A}, X.Adj x y → Y.Adj (f x) (f y)) :
    Nat.card X.edgeSet ≤ Nat.card Y.edgeSet := by
  exact Nat.card_le_card_of_injective (edgeMapOfInjectiveHom X Y f hfadj)
    (edgeMapOfInjectiveHom_injective X Y f hfadj)

private lemma injective_hom_reflects_adj_of_edge_card_eq {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B]
    (f : A ↪ B)
    (hfadj : ∀ {x y : A}, X.Adj x y → Y.Adj (f x) (f y))
    (hedge : Nat.card X.edgeSet = Nat.card Y.edgeSet) :
    ∀ {x y : A}, Y.Adj (f x) (f y) → X.Adj x y := by
  classical
  letI : Fintype X.edgeSet := (Set.toFinite X.edgeSet).fintype
  letI : Fintype Y.edgeSet := (Set.toFinite Y.edgeSet).fintype
  have hcardF :
      Fintype.card X.edgeSet = Fintype.card Y.edgeSet := by
    simpa [Nat.card_eq_fintype_card] using hedge
  have hbij :
      Function.Bijective (edgeMapOfInjectiveHom X Y f hfadj) :=
    (Fintype.bijective_iff_injective_and_card
      (edgeMapOfInjectiveHom X Y f hfadj)).mpr
        ⟨edgeMapOfInjectiveHom_injective X Y f hfadj, hcardF⟩
  intro x y hxy
  let eY : Y.edgeSet := ⟨s(f x, f y), (SimpleGraph.mem_edgeSet Y).mpr hxy⟩
  obtain ⟨eX, heX⟩ := hbij.2 eY
  have hsym :
      f.sym2Map (eX : Sym2 A) = s(f x, f y) := by
    exact congrArg (fun e : Y.edgeSet => (e : Sym2 B)) heX
  rcases eX with ⟨se, hse⟩
  induction se using Sym2.inductionOn with
  | hf a b =>
      rw [Function.Embedding.sym2Map_apply, Sym2.map_mk] at hsym
      rcases Sym2.eq_iff.mp hsym with h | h
      · have hax : a = x := f.injective h.1
        have hby : b = y := f.injective h.2
        rw [← hax, ← hby]
        exact (SimpleGraph.mem_edgeSet X).mp hse
      · have hay : a = y := f.injective h.1
        have hbx : b = x := f.injective h.2
        rw [← hbx, ← hay]
        exact ((SimpleGraph.mem_edgeSet X).mp hse).symm

theorem graph_iso_of_bijective_homs {A : Type u} {B : Type v}
    (X : SimpleGraph A) (Y : SimpleGraph B) [Finite A] [Finite B]
    (f : A ↪ B) (g : B ↪ A)
    (hfbij : Function.Bijective f) (_hgbij : Function.Bijective g)
    (hfadj : ∀ {x y : A}, X.Adj x y → Y.Adj (f x) (f y))
    (hgadj : ∀ {x y : B}, Y.Adj x y → X.Adj (g x) (g y)) :
    Nonempty (X ≃g Y) := by
  classical
  have hXYedge := edge_card_le_of_injective_hom X Y f hfadj
  have hYXedge := edge_card_le_of_injective_hom Y X g hgadj
  have hedge : Nat.card X.edgeSet = Nat.card Y.edgeSet :=
    le_antisymm hXYedge hYXedge
  let e : A ≃ B := Equiv.ofBijective (f : A → B) hfbij
  refine ⟨RelIso.mk e ?_⟩
  intro x y
  constructor
  · intro h
    exact injective_hom_reflects_adj_of_edge_card_eq X Y f hfadj hedge h
  · intro h
    exact hfadj h

end Chapter01
end Diestel
