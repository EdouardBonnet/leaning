import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

open Diestel.Chapter01

universe u

namespace GallaiEdmondsAux

variable {V : Type u}

lemma odd_natCard_of_factorCritical (G : SimpleGraph V) [Finite V]
    (hG : IsFactorCritical G) :
    Odd (Nat.card V) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rcases hG.1 with ⟨v⟩
  rcases hG.2.2 v with ⟨M, hM⟩
  have hEvenDelete : Even (Fintype.card {w : V // w ≠ v}) := hM.even_card
  have hDeleteCard : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 :=
    Set.card_ne_eq v
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hDeleteAdd : Fintype.card {w : V // w ≠ v} + 1 = Fintype.card V := by
    rw [hDeleteCard, Nat.sub_add_cancel hpos]
  rw [Nat.card_eq_fintype_card, ← hDeleteAdd]
  exact hEvenDelete.add_one

lemma odd_supp_ncard_of_factorCritical_component (G : SimpleGraph V) [Finite V]
    (C : G.ConnectedComponent) (hC : IsFactorCritical C.toSimpleGraph) :
    Odd C.supp.ncard := by
  have hOdd : Odd (Nat.card C) := odd_natCard_of_factorCritical C.toSimpleGraph hC
  simpa [Nat.card_coe_set_eq] using hOdd

lemma deletedComponent_mem_oddComponents_of_gallaiEdmondsSet
    (G : SimpleGraph V) [Finite V] {S : Set V} (hS : GallaiEdmondsSet G S)
    (C : DeletedComponent G S) :
    C ∈ (delete_vertices G S).oddComponents :=
  odd_supp_ncard_of_factorCritical_component (delete_vertices G S) C (hS.2 C)

lemma ncard_le_deletedComponent_card_of_matchable
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hS : MatchableToDeletedComponents G S) :
    S.ncard ≤ Nat.card (DeletedComponent G S) := by
  rcases hS with ⟨f, hf_inj, _hf_adj⟩
  simpa [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf_inj

lemma deletedComponent_card_eq_oddComponents_ncard_of_gallaiEdmondsSet
    (G : SimpleGraph V) [Finite V] {S : Set V} (hS : GallaiEdmondsSet G S) :
    Nat.card (DeletedComponent G S) = (delete_vertices G S).oddComponents.ncard := by
  have hOddAll : (delete_vertices G S).oddComponents = Set.univ := by
    exact Set.eq_univ_iff_forall.mpr
      (deletedComponent_mem_oddComponents_of_gallaiEdmondsSet G hS)
  rw [hOddAll, Set.ncard_univ]

lemma perfectMatching_matches_deletedComponent_to_S
    {G : SimpleGraph V} [Finite V] {S : Set V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) (C : DeletedComponent G S)
    (hC : IsFactorCritical C.toSimpleGraph) :
    ∃ s : S, ∃ x : C, M.Adj x.1.1 s.1 := by
  classical
  by_contra hnone
  let D := delete_vertices G S
  let N : C.toSimpleGraph.Subgraph := {
    verts := Set.univ
    Adj := fun (x y : C) => M.Adj x.1.1 y.1.1
    adj_sub := by
      intro x y hxy
      change D.Adj x.1 y.1
      simpa [D, delete_vertices] using hxy.adj_sub
    edge_vert := by
      intro x y hxy
      simp
    symm := by
      intro x y hxy
      exact hxy.symm }
  have hNpm : N.IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    obtain ⟨y, hxy, hyuniq⟩ :=
      (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) x.1.1
    have hyS : y ∉ S := by
      intro hyS
      exact hnone ⟨⟨y, hyS⟩, x, hxy⟩
    let yD : (Sᶜ : Set V) := ⟨y, hyS⟩
    have hxyD : D.Adj x.1 yD := by
      simpa [D, delete_vertices, yD] using hxy.adj_sub
    have hyCmem : yD ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxyD
    let yC : C := ⟨yD, hyCmem⟩
    refine ⟨yC, ?_, ?_⟩
    · exact hxy
    · intro z hz
      apply Subtype.ext
      apply Subtype.ext
      exact hyuniq z.1.1 hz
  exact hC.2.1 N hNpm

lemma deletedComponent_card_le_ncard_of_isPerfectMatching
    {G : SimpleGraph V} [Finite V] {S : Set V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) (hS : GallaiEdmondsSet G S) :
    Nat.card (DeletedComponent G S) ≤ S.ncard := by
  classical
  choose s hs using fun C : DeletedComponent G S =>
    perfectMatching_matches_deletedComponent_to_S (G := G) (S := S) hM C (hS.2 C)
  choose x hx using hs
  have hs_inj : Function.Injective s := by
    intro C D hCD
    have hxD : M.Adj (x D).1.1 (s C).1 := by
      simpa [hCD] using hx D
    have hvertex : (x C).1.1 = (x D).1.1 := hM.1.eq_of_adj_right (hx C) hxD
    refine SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := (x C).1) (x C).2 ?_
    have hsub : (x C).1 = (x D).1 := Subtype.ext hvertex
    simpa [hsub] using (x D).2
  have hle : Nat.card (DeletedComponent G S) ≤ Nat.card S :=
    Nat.card_le_card_of_injective s hs_inj
  simpa [Nat.card_coe_set_eq] using hle

lemma ncard_eq_deletedComponent_card_of_isPerfectMatching
    {G : SimpleGraph V} [Finite V] {S : Set V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) (hS : GallaiEdmondsSet G S) :
    S.ncard = Nat.card (DeletedComponent G S) := by
  exact le_antisymm
    (ncard_le_deletedComponent_card_of_matchable G hS.1)
    (deletedComponent_card_le_ncard_of_isPerfectMatching hM hS)

lemma matchable_bijective_of_ncard_eq
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (hMatch : MatchableToDeletedComponents G S)
    (hEq : S.ncard = Nat.card (DeletedComponent G S)) :
    ∃ f : S → DeletedComponent G S, Function.Bijective f ∧
      ∀ s : S, ∃ x : (f s).supp, G.Adj s.1 x.1.1 := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (DeletedComponent G S) := Fintype.ofFinite (DeletedComponent G S)
  rcases hMatch with ⟨f, hf_inj, hf_adj⟩
  have hcard : Fintype.card S = Fintype.card (DeletedComponent G S) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [Nat.card_coe_set_eq]
    exact hEq
  refine ⟨f, ?_, hf_adj⟩
  exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩

lemma internal_deleted_matching_adj_sub
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (C : DeletedComponent G S) (x : C)
    (N : (deleteVertex C.toSimpleGraph x).Subgraph)
    {y z : {w : C // w ≠ x}} (hyz : N.Adj y z) :
    G.Adj y.1.1.1 z.1.1.1 := by
  simpa [deleteVertex, delete_vertices, SimpleGraph.ConnectedComponent.toSimpleGraph,
    SimpleGraph.induce] using hyz.adj_sub

lemma exists_isPerfectMatching_of_gallaiEdmondsSet_ncard_eq
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (hS : GallaiEdmondsSet G S)
    (hEq : S.ncard = Nat.card (DeletedComponent G S)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨f, hf_bij, hf_adj⟩ := matchable_bijective_of_ncard_eq hS.1 hEq
  choose x hx using hf_adj
  let root : (s : S) → f s := fun s => ⟨(x s).1, (x s).2⟩
  choose N hN using fun s : S => (hS.2 (f s)).2.2 (root s)
  let MAdj : V → V → Prop := fun u v =>
    (∃ s : S, u = s.1 ∧ v = (root s).1.1) ∨
      (∃ s : S, u = (root s).1.1 ∧ v = s.1) ∨
        ∃ s : S, ∃ y z : {w : f s // w ≠ root s},
          (N s).Adj y z ∧ u = y.1.1.1 ∧ v = z.1.1.1
  have same_index_of_common_vertex :
      ∀ {s t : S} {y : f s} {z : f t},
        y.1.1 = z.1.1 → s = t := by
    intro s t y z hyz
    apply hf_bij.1
    refine SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := y.1) y.2 ?_
    have hsub : y.1 = z.1 := Subtype.ext hyz
    simpa [hsub] using z.2
  let M : G.Subgraph := {
    verts := Set.univ
    Adj := MAdj
    adj_sub := by
      intro u v huv
      rcases huv with ⟨s, rfl, rfl⟩ | ⟨s, rfl, rfl⟩ |
        ⟨s, y, z, hyz, rfl, rfl⟩
      · exact hx s
      · exact (hx s).symm
      · exact internal_deleted_matching_adj_sub (G := G) (S := S) (f s) (root s) (N s) hyz
    edge_vert := by
      intro u v huv
      simp
    symm := by
      intro u v huv
      rcases huv with ⟨s, hu, hv⟩ | ⟨s, hu, hv⟩ | ⟨s, y, z, hyz, hu, hv⟩
      · exact Or.inr (Or.inl ⟨s, hv, hu⟩)
      · exact Or.inl ⟨s, hv, hu⟩
      · exact Or.inr (Or.inr ⟨s, z, y, hyz.symm, hv, hu⟩) }
  refine ⟨M, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  by_cases hvS : v ∈ S
  · let s₀ : S := ⟨v, hvS⟩
    refine ⟨(root s₀).1.1, ?_, ?_⟩
    · change MAdj v (root s₀).1.1
      exact Or.inl ⟨s₀, rfl, rfl⟩
    · intro w hw
      change MAdj v w at hw
      rcases hw with ⟨t, hvt, hwt⟩ | ⟨t, hvr, hwt⟩ | ⟨t, y, z, _hyz, hvy, _hwz⟩
      · have ht : t = s₀ := Subtype.ext (by simpa [s₀] using hvt.symm)
        subst t
        simpa using hwt
      · exfalso
        exact (root t).1.2 (by simpa [hvr] using hvS)
      · exfalso
        exact y.1.1.2 (by simpa [hvy] using hvS)
  · let vD : (Sᶜ : Set V) := ⟨v, hvS⟩
    let C : DeletedComponent G S := (delete_vertices G S).connectedComponentMk vD
    obtain ⟨s₀, hs₀⟩ := hf_bij.2 C
    have hvC : vD ∈ C.supp := rfl
    have hvfs : vD ∈ (f s₀).supp := by
      simpa [hs₀] using hvC
    let vc : f s₀ := ⟨vD, hvfs⟩
    by_cases hroot : vc = root s₀
    · have hvr : v = (root s₀).1.1 := by
        simpa [vc, vD] using congrArg (fun y : f s₀ => y.1.1) hroot
      refine ⟨s₀.1, ?_, ?_⟩
      · change MAdj v s₀.1
        exact Or.inr (Or.inl ⟨s₀, hvr, rfl⟩)
      · intro w hw
        change MAdj v w at hw
        rcases hw with ⟨t, hvt, _hwt⟩ | ⟨t, hvr_t, hwt⟩ |
          ⟨t, y, _z, _hyz, hvy, _hwz⟩
        · exfalso
          exact hvS (by simpa [hvt] using t.2)
        · have hroot_eq : (root s₀).1.1 = (root t).1.1 := by
            calc
              (root s₀).1.1 = v := hvr.symm
              _ = (root t).1.1 := hvr_t
          have hst : s₀ = t := same_index_of_common_vertex hroot_eq
          simpa [← hst] using hwt
        · have hroot_y : (root s₀).1.1 = y.1.1.1 := by
            calc
              (root s₀).1.1 = v := hvr.symm
              _ = y.1.1.1 := hvy
          have hst : s₀ = t := same_index_of_common_vertex hroot_y
          subst t
          have hyroot : y.1 = root s₀ := Subtype.ext (Subtype.ext hroot_y.symm)
          exact (y.2 hyroot).elim
    · let yv : {w : f s₀ // w ≠ root s₀} := ⟨vc, hroot⟩
      obtain ⟨z₀, hz₀, hzuniq⟩ :=
        (SimpleGraph.Subgraph.isPerfectMatching_iff.mp (hN s₀)) yv
      refine ⟨z₀.1.1.1, ?_, ?_⟩
      · change MAdj v z₀.1.1.1
        exact Or.inr (Or.inr ⟨s₀, yv, z₀, hz₀, rfl, rfl⟩)
      · intro w hw
        change MAdj v w at hw
        rcases hw with ⟨t, hvt, _hwt⟩ | ⟨t, hvr_t, _hwt⟩ |
          ⟨t, y, z, hyz, hvy, hwz⟩
        · exfalso
          exact hvS (by simpa [hvt] using t.2)
        · have hvc_root_t : vc.1.1 = (root t).1.1 := by
            simpa [vc, vD] using hvr_t
          have hst : s₀ = t := same_index_of_common_vertex hvc_root_t
          subst t
          have hvc_root : vc = root s₀ := Subtype.ext (Subtype.ext hvc_root_t)
          exact (hroot hvc_root).elim
        · have hvc_y : vc.1.1 = y.1.1.1 := by
            simpa [vc, vD] using hvy
          have hst : s₀ = t := same_index_of_common_vertex hvc_y
          subst t
          have hy_eq : y = yv := by
            apply Subtype.ext
            exact Subtype.ext (Subtype.ext hvc_y.symm)
          have hz_eq : z = z₀ := hzuniq z (by simpa [hy_eq] using hyz)
          simpa [hz_eq] using hwz

lemma isPerfectMatching_iff_ncard_eq_of_gallaiEdmondsSet
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (hS : GallaiEdmondsSet G S) :
    ((∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      S.ncard = Nat.card (DeletedComponent G S)) := by
  constructor
  · rintro ⟨M, hM⟩
    exact ncard_eq_deletedComponent_card_of_isPerfectMatching hM hS
  · exact exists_isPerfectMatching_of_gallaiEdmondsSet_ncard_eq hS

end GallaiEdmondsAux

end Chapter02
end Diestel
