import Chapter02.tree_packing_aux
import Chapter02.multigraph_tree_shadow_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma isQuotientSpanningTree_ncard_eq
    {G : MultiGraph V E} {P : Finset (Set V)} {F : Set (G.CrossEdge P)}
    (hF : G.IsQuotientSpanningTree P F) :
    F.ncard = P.card - 1 := by
  rcases hF with ⟨_hfinite, hempty | hconn⟩
  · rcases hempty with ⟨hP, hFempty⟩
    simp [hP, hFempty]
  · omega

lemma isQuotientSpanningTree_natCard_eq
    {G : MultiGraph V E} [Finite E] {P : Finset (Set V)} {F : Set (G.CrossEdge P)}
    (hF : G.IsQuotientSpanningTree P F) :
    Nat.card F = P.card - 1 := by
  calc
    Nat.card F = F.ncard :=
      TreeShadow.natCard_subtype_eq_ncard (F := F)
    _ = P.card - 1 := isQuotientSpanningTree_ncard_eq (G := G) hF

lemma quotient_cover_edgeDisjoint_of_partition_bound
    {G : MultiGraph V E} [Finite E] {P : Finset (Set V)} {k : ℕ}
    {Q : Fin k → Set (G.CrossEdge P)}
    (hTrees : ∀ i : Fin k, G.IsQuotientSpanningTree P (Q i))
    (hcover : ∀ e : G.CrossEdge P, ∃ i : Fin k, e ∈ Q i)
    (hbound : k * (P.card - 1) ≤ G.crossEdgeCount P) :
    EdgeDisjointFamily Q := by
  classical
  let D := Sigma fun i : Fin k => {e : G.CrossEdge P // e ∈ Q i}
  let proj : D → G.CrossEdge P := fun x => x.2.1
  have hsurj : Function.Surjective proj := by
    intro e
    rcases hcover e with ⟨i, hei⟩
    exact ⟨⟨i, ⟨e, hei⟩⟩, rfl⟩
  have hcross_le_D : Nat.card (G.CrossEdge P) ≤ Nat.card D :=
    Nat.card_le_card_of_surjective proj hsurj
  have hD_eq : Nat.card D = k * (P.card - 1) := by
    rw [Nat.card_sigma]
    calc
      (∑ i : Fin k, Nat.card {e : G.CrossEdge P // e ∈ Q i}) =
          ∑ _i : Fin k, (P.card - 1) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact isQuotientSpanningTree_natCard_eq (G := G) (hTrees i)
      _ = k * (P.card - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hD_le_cross : Nat.card D ≤ Nat.card (G.CrossEdge P) := by
    rw [hD_eq]
    simpa [crossEdgeCount, CrossEdge] using hbound
  have hD_card : Nat.card D = Nat.card (G.CrossEdge P) :=
    le_antisymm hD_le_cross hcross_le_D
  haveI : Fintype D := Fintype.ofFinite D
  haveI : Fintype (G.CrossEdge P) := Fintype.ofFinite (G.CrossEdge P)
  have hcard : Fintype.card D = Fintype.card (G.CrossEdge P) := by
    calc
      Fintype.card D = Nat.card D := (Nat.card_eq_fintype_card).symm
      _ = Nat.card (G.CrossEdge P) := hD_card
      _ = Fintype.card (G.CrossEdge P) := Nat.card_eq_fintype_card
  have hinj : Function.Injective proj :=
    ((Fintype.bijective_iff_surjective_and_card proj).2 ⟨hsurj, hcard⟩).1
  intro i j hij
  rw [Set.disjoint_left]
  intro e hei hej
  let xi : D := ⟨i, ⟨e, hei⟩⟩
  let xj : D := ⟨j, ⟨e, hej⟩⟩
  have hx : proj xi = proj xj := rfl
  have hxi : xi = xj := hinj hx
  exact hij (congrArg Sigma.fst hxi)

end MultiGraph

end Chapter02
end Diestel
