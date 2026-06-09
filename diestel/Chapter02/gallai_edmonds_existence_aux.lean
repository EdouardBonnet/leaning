import Chapter02.gallai_edmonds_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

open Diestel.Chapter01

universe u v

namespace GallaiEdmondsExistence

variable {V : Type u}

/-- The Tutte defect `q(G - S) - |S|`, using Chapter 2's deleted-graph model. -/
noncomputable def defect (G : SimpleGraph V) [Finite V] (S : Set V) : ℤ :=
  ((delete_vertices G S).oddComponents.ncard : ℤ) - S.ncard

lemma exists_largest_max_defect_set (G : SimpleGraph V) [Finite V] :
    ∃ S : Set V,
      (∀ T : Set V, defect G T ≤ defect G S) ∧
        ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard := by
  classical
  have hfinite_all : (Set.univ : Set (Set V)).Finite := Set.toFinite Set.univ
  have hnonempty_all : (Set.univ : Set (Set V)).Nonempty := ⟨∅, by simp⟩
  obtain ⟨S₀, hS₀max⟩ :=
    hfinite_all.exists_maximalFor (defect G) (Set.univ : Set (Set V)) hnonempty_all
  have hdef_le_S₀ : ∀ T : Set V, defect G T ≤ defect G S₀ := by
    intro T
    rcases le_total (defect G T) (defect G S₀) with hle | hle
    · exact hle
    · exact hS₀max.2 (by simp) hle
  let maxSets : Set (Set V) := {T | defect G T = defect G S₀}
  have hfinite_maxSets : maxSets.Finite := Set.toFinite maxSets
  have hnonempty_maxSets : maxSets.Nonempty := ⟨S₀, rfl⟩
  obtain ⟨S, hSmax⟩ :=
    hfinite_maxSets.exists_maximalFor Set.ncard maxSets hnonempty_maxSets
  refine ⟨S, ?_, ?_⟩
  · intro T
    rw [hSmax.1]
    exact hdef_le_S₀ T
  · intro T hT
    rcases le_total T.ncard S.ncard with hle | hle
    · exact hle
    · exact hSmax.2 (hT.trans hSmax.1) hle

lemma oddComponents_nonempty_of_odd_natCard (G : SimpleGraph V) [Finite V]
    (hOdd : Odd (Nat.card V)) :
    G.oddComponents.Nonempty := by
  have hOddComponents : Odd G.oddComponents.ncard :=
    (SimpleGraph.odd_ncard_oddComponents G).2 hOdd
  exact (Set.ncard_pos (s := G.oddComponents)).mp hOddComponents.pos

lemma odd_natCard_delete_vertex_of_even_natCard {α : Type u} [Finite α]
    (hEven : Even (Nat.card α)) (a : α) :
    Odd (Nat.card {b : α // b ≠ a}) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hDeleteCard : Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 :=
    by simpa using (Set.card_ne_eq a)
  have hEvenCard : Even (Fintype.card α) := by
    rwa [Nat.card_eq_fintype_card] at hEven
  have hpos : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  have hOddDelete : Odd (Fintype.card α - 1) :=
    Nat.Even.sub_odd hpos hEvenCard odd_one
  rw [Nat.card_eq_fintype_card, hDeleteCard]
  exact hOddDelete

lemma even_natCard_delete_vertex_of_odd_natCard {α : Type u} [Finite α]
    (hOdd : Odd (Nat.card α)) (a : α) :
    Even (Nat.card {b : α // b ≠ a}) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hDeleteCard : Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 :=
    by simpa using (Set.card_ne_eq a)
  have hOddCard : Odd (Fintype.card α) := by
    rwa [Nat.card_eq_fintype_card] at hOdd
  have hEvenDelete : Even (Fintype.card α - 1) :=
    Nat.Odd.sub_odd hOddCard odd_one
  rw [Nat.card_eq_fintype_card, hDeleteCard]
  exact hEvenDelete

lemma odd_natCard_deleteVertex_of_even_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hEven : Even C.supp.ncard) (c : C) :
    Odd (Nat.card {w : C // w ≠ c}) := by
  have hEvenCard : Even (Nat.card C) := by
    simpa [Nat.card_coe_set_eq] using hEven
  exact odd_natCard_delete_vertex_of_even_natCard hEvenCard c

lemma even_natCard_deleteVertex_of_odd_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hOdd : Odd C.supp.ncard) (c : C) :
    Even (Nat.card {w : C // w ≠ c}) := by
  have hOddCard : Odd (Nat.card C) := by
    simpa [Nat.card_coe_set_eq] using hOdd
  exact even_natCard_delete_vertex_of_odd_natCard hOddCard c

lemma oddComponents_deleteVertex_nonempty_of_even_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hEven : Even C.supp.ncard) (c : C) :
    (deleteVertex C.toSimpleGraph c).oddComponents.Nonempty :=
  oddComponents_nonempty_of_odd_natCard (deleteVertex C.toSimpleGraph c)
    (odd_natCard_deleteVertex_of_even_component G C hEven c)

lemma reachable_to_deleteVertex_of_component_not_mem
    {G : SimpleGraph V} {C : G.ConnectedComponent} {v x y : V}
    (hvC : v ∉ C.supp) (hxC : x ∈ C.supp) (hxy : G.Reachable x y) :
    ∃ hy : y ≠ v,
      (deleteVertex G v).Reachable
        ⟨x, fun hxv => hvC (by simpa [hxv] using hxC)⟩ ⟨y, hy⟩ := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil =>
      exact ⟨fun hxv => hvC (by simpa [← hxv] using hxC), SimpleGraph.Walk.nil.reachable⟩
  | cons hxy p ih =>
      rename_i x z y
      have hzC : z ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hxy
      have hx_ne : x ≠ v := fun hxv => hvC (by simpa [← hxv] using hxC)
      have hz_ne : z ≠ v := fun hzv => hvC (by simpa [← hzv] using hzC)
      obtain ⟨hy_ne, hReachD⟩ := ih hzC
      obtain ⟨pD⟩ := hReachD
      let xD : {w : V // w ≠ v} := ⟨x, hx_ne⟩
      let zD : {w : V // w ≠ v} := ⟨z, hz_ne⟩
      have hxzD : (deleteVertex G v).Adj xD zD := by
        simpa [deleteVertex, xD, zD] using hxy
      exact ⟨hy_ne, (SimpleGraph.Walk.cons hxzD pD).reachable⟩

def deleteVertexHom (G : SimpleGraph V) (v : V) :
    deleteVertex G v →g G where
  toFun x := x.1
  map_rel' := by
    intro x y hxy
    simpa [deleteVertex] using hxy

noncomputable def componentMapDeleteVertex
    (G : SimpleGraph V) [Finite V] {v : V}
    (C : G.ConnectedComponent) (hvC : v ∉ C.supp) :
    (deleteVertex G v).ConnectedComponent :=
  let r := C.nonempty_supp.some
  (deleteVertex G v).connectedComponentMk
    ⟨r, fun hrv => hvC (by simpa [← hrv] using C.nonempty_supp.some_mem)⟩

noncomputable def componentDeleteVertexSuppEquiv
    (G : SimpleGraph V) [Finite V] {v : V}
    (C : G.ConnectedComponent) (hvC : v ∉ C.supp) :
    C.supp ≃ (componentMapDeleteVertex G C hvC).supp where
  toFun x := by
    let r := C.nonempty_supp.some
    let rD : {w : V // w ≠ v} :=
      ⟨r, fun hrv => hvC (by simpa [← hrv] using C.nonempty_supp.some_mem)⟩
    have hxC : x.1 ∈ C.supp := x.2
    have hrC : r ∈ C.supp := C.nonempty_supp.some_mem
    have hcc : G.connectedComponentMk x.1 = G.connectedComponentMk r := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxC hrC
      rw [hxC, hrC]
    exact ⟨⟨x.1, fun hxv => hvC (by simpa [hxv] using x.2)⟩,
      by
        have hReach := SimpleGraph.ConnectedComponent.exact hcc
        obtain ⟨hr_ne, hReachD⟩ :=
          reachable_to_deleteVertex_of_component_not_mem (C := C) hvC x.2 hReach
        have hccD :
            (deleteVertex G v).connectedComponentMk
                ⟨x.1, fun hxv => hvC (by simpa [hxv] using x.2)⟩ =
              (deleteVertex G v).connectedComponentMk ⟨r, hr_ne⟩ :=
          SimpleGraph.ConnectedComponent.sound hReachD
        have hroot : (⟨r, hr_ne⟩ : {w : V // w ≠ v}) = rD := by
          apply Subtype.ext
          rfl
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff
          (componentMapDeleteVertex G C hvC)
          ⟨x.1, fun hxv => hvC (by simpa [hxv] using x.2)⟩).2
          (by simpa [componentMapDeleteVertex, r, rD, hroot] using hccD)⟩
  invFun y := by
    let r := C.nonempty_supp.some
    let rD : {w : V // w ≠ v} :=
      ⟨r, fun hrv => hvC (by simpa [← hrv] using C.nonempty_supp.some_mem)⟩
    have hrC : r ∈ C.supp := C.nonempty_supp.some_mem
    have hycc :
        (deleteVertex G v).connectedComponentMk y.1 =
          componentMapDeleteVertex G C hvC := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (componentMapDeleteVertex G C hvC) y.1).1 y.2
    have hccD :
        (deleteVertex G v).connectedComponentMk y.1 =
          (deleteVertex G v).connectedComponentMk rD := by
      simpa [componentMapDeleteVertex, r, rD] using hycc
    exact ⟨y.1.1, by
      obtain ⟨pD⟩ := SimpleGraph.ConnectedComponent.exact hccD
      have pG : G.Walk y.1.1 r := pD.map (deleteVertexHom G v)
      have hccG : G.connectedComponentMk y.1.1 = G.connectedComponentMk r :=
        SimpleGraph.ConnectedComponent.sound pG.reachable
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hrEq : G.connectedComponentMk r = C := by
        simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff C r).1 hrC
      exact hccG.trans hrEq⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

lemma odd_componentMapDeleteVertex_of_not_mem
    (G : SimpleGraph V) [Finite V] {v : V}
    (C : G.ConnectedComponent) (hvC : v ∉ C.supp)
    (hOdd : Odd C.supp.ncard) :
    Odd (componentMapDeleteVertex G C hvC).supp.ncard := by
  have hcard : C.supp.ncard = (componentMapDeleteVertex G C hvC).supp.ncard := by
    simpa [Nat.card_coe_set_eq] using
      Nat.card_congr (componentDeleteVertexSuppEquiv G C hvC)
  rwa [← hcard]

lemma componentMapDeleteVertex_eq_imp_eq
    (G : SimpleGraph V) [Finite V] {v : V}
    {C D : G.ConnectedComponent} (hvC : v ∉ C.supp) (hvD : v ∉ D.supp)
    (hEq : componentMapDeleteVertex G C hvC = componentMapDeleteVertex G D hvD) :
    C = D := by
  let rC := C.nonempty_supp.some
  let rCD : {w : V // w ≠ v} :=
    ⟨rC, fun hrv => hvC (by simpa [← hrv] using C.nonempty_supp.some_mem)⟩
  have hrC : rC ∈ C.supp := C.nonempty_supp.some_mem
  have hrCmap : rCD ∈ (componentMapDeleteVertex G C hvC).supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (componentMapDeleteVertex G C hvC) rCD).2 (by
        simp [componentMapDeleteVertex, rC, rCD])
  have hrDmap : rCD ∈ (componentMapDeleteVertex G D hvD).supp := by
    simpa [hEq] using hrCmap
  let yD : (componentMapDeleteVertex G D hvD).supp := ⟨rCD, hrDmap⟩
  let eD := componentDeleteVertexSuppEquiv G D hvD
  have hrD : rC ∈ D.supp := by
    have hval : (eD.symm yD).1 = rC := rfl
    rw [← hval]
    exact (eD.symm yD).2
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hrC hrD

lemma oddComponents_not_mem_even_component_vertex
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hEven : Even C.supp.ncard) (c : C)
    {K : G.ConnectedComponent} (hK : K ∈ G.oddComponents) :
    c.1 ∉ K.supp := by
  intro hcK
  have hKC : K = C :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex hcK c.2
  have hOddC : Odd C.supp.ncard := by
    simpa [hKC] using hK
  exact (Nat.not_even_iff_odd.2 hOddC) hEven

lemma oddComponents_ncard_le_deleteVertex_of_even_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hEven : Even C.supp.ncard) (c : C) :
    G.oddComponents.ncard ≤ (deleteVertex G c.1).oddComponents.ncard := by
  classical
  let source : Set G.ConnectedComponent :=
    {K | K ∈ G.oddComponents ∧ c.1 ∉ K.supp}
  let f : source → (deleteVertex G c.1).oddComponents := fun K =>
    ⟨componentMapDeleteVertex G K.1 K.2.2,
      odd_componentMapDeleteVertex_of_not_mem G K.1 K.2.2 K.2.1⟩
  have hf : Function.Injective f := by
    intro K L hKL
    apply Subtype.ext
    exact componentMapDeleteVertex_eq_imp_eq G K.2.2 L.2.2 (congrArg Subtype.val hKL)
  have hsource_eq : source = G.oddComponents := by
    ext K
    constructor
    · intro hK
      exact hK.1
    · intro hK
      exact ⟨hK, oddComponents_not_mem_even_component_vertex G C hEven c hK⟩
  have hle : source.ncard ≤ (deleteVertex G c.1).oddComponents.ncard := by
    simpa [source, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf
  simpa [hsource_eq] using hle

lemma reachable_to_component_deleteVertex_of_component
    {G : SimpleGraph V} (C : G.ConnectedComponent) (c : C)
    {x y : {w : V // w ≠ c.1}}
    (hxC : x.1 ∈ C.supp) (hxy : (deleteVertex G c.1).Reachable x y) :
    ∃ hyC : y.1 ∈ C.supp,
      (deleteVertex C.toSimpleGraph c).Reachable
        ⟨⟨x.1, hxC⟩, fun hxc => x.2 (congrArg Subtype.val hxc)⟩
        ⟨⟨y.1, hyC⟩, fun hyc => y.2 (congrArg Subtype.val hyc)⟩ := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil =>
      exact ⟨hxC, SimpleGraph.Walk.nil.reachable⟩
  | cons hxy p ih =>
      rename_i x z y
      have hxzG : G.Adj x.1 z.1 := by
        simpa [deleteVertex] using hxy
      have hzC : z.1 ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hxzG
      obtain ⟨hyC, hReachLocal⟩ := ih hzC
      obtain ⟨pLocal⟩ := hReachLocal
      let xLocal : {w : C // w ≠ c} :=
        ⟨⟨x.1, hxC⟩, fun hxc => x.2 (congrArg Subtype.val hxc)⟩
      let zLocal : {w : C // w ≠ c} :=
        ⟨⟨z.1, hzC⟩, fun hzc => z.2 (congrArg Subtype.val hzc)⟩
      have hxzLocal : (deleteVertex C.toSimpleGraph c).Adj xLocal zLocal := by
        change C.toSimpleGraph.Adj xLocal.1 zLocal.1
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph, xLocal, zLocal] using hxzG
      exact ⟨hyC, (SimpleGraph.Walk.cons hxzLocal pLocal).reachable⟩

def componentDeleteVertexToGlobalHom
    (G : SimpleGraph V) (C : G.ConnectedComponent) (c : C) :
    deleteVertex C.toSimpleGraph c →g deleteVertex G c.1 where
  toFun x := ⟨x.1.1, fun hxc => x.2 (Subtype.ext hxc)⟩
  map_rel' := by
    intro x y hxy
    have hlocal : C.toSimpleGraph.Adj x.1 y.1 := by
      simpa [deleteVertex] using hxy
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hlocal

noncomputable def componentDeleteVertexComponentMap
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent) (c : C)
    (D : (deleteVertex C.toSimpleGraph c).ConnectedComponent) :
    (deleteVertex G c.1).ConnectedComponent :=
  let r := D.nonempty_supp.some
  (deleteVertex G c.1).connectedComponentMk
    (componentDeleteVertexToGlobalHom G C c r)

noncomputable def componentDeleteVertexGlobalSuppEquiv
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent) (c : C)
    (D : (deleteVertex C.toSimpleGraph c).ConnectedComponent) :
    D.supp ≃ (componentDeleteVertexComponentMap G C c D).supp where
  toFun x := by
    let r := D.nonempty_supp.some
    have hxD : x.1 ∈ D.supp := x.2
    have hrD : r ∈ D.supp := D.nonempty_supp.some_mem
    have hcc : (deleteVertex C.toSimpleGraph c).connectedComponentMk x.1 =
        (deleteVertex C.toSimpleGraph c).connectedComponentMk r := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxD hrD
      rw [hxD, hrD]
    exact ⟨componentDeleteVertexToGlobalHom G C c x.1, by
      have hReach := SimpleGraph.ConnectedComponent.exact hcc
      have hReachGlobal : (deleteVertex G c.1).Reachable
          (componentDeleteVertexToGlobalHom G C c x.1)
          (componentDeleteVertexToGlobalHom G C c r) :=
        hReach.map (componentDeleteVertexToGlobalHom G C c)
      have hccGlobal :
          (deleteVertex G c.1).connectedComponentMk
              (componentDeleteVertexToGlobalHom G C c x.1) =
            (deleteVertex G c.1).connectedComponentMk
              (componentDeleteVertexToGlobalHom G C c r) :=
        SimpleGraph.ConnectedComponent.sound hReachGlobal
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (componentDeleteVertexComponentMap G C c D)
        (componentDeleteVertexToGlobalHom G C c x.1)).2
        (by simpa [componentDeleteVertexComponentMap, r] using hccGlobal)⟩
  invFun y := by
    let r := D.nonempty_supp.some
    let rGlobal := componentDeleteVertexToGlobalHom G C c r
    have hrD : r ∈ D.supp := D.nonempty_supp.some_mem
    have hycc :
        (deleteVertex G c.1).connectedComponentMk y.1 =
          componentDeleteVertexComponentMap G C c D := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (componentDeleteVertexComponentMap G C c D) y.1).1 y.2
    have hccGlobal :
        (deleteVertex G c.1).connectedComponentMk rGlobal =
          (deleteVertex G c.1).connectedComponentMk y.1 := by
      simpa [componentDeleteVertexComponentMap, r, rGlobal] using hycc.symm
    exact ⟨⟨⟨y.1.1, by
      have hReachGlobal := SimpleGraph.ConnectedComponent.exact hccGlobal
      have hrGlobalC : rGlobal.1 ∈ C.supp := by
        change r.1.1 ∈ C.supp
        exact r.1.2
      obtain ⟨hyC, _hReachLocal⟩ :=
        reachable_to_component_deleteVertex_of_component C c
          (x := rGlobal) (y := y.1) hrGlobalC hReachGlobal
      exact hyC⟩, fun hyc => y.1.2 (congrArg Subtype.val hyc)⟩, by
      have hReachGlobal := SimpleGraph.ConnectedComponent.exact hccGlobal
      have hrGlobalC : rGlobal.1 ∈ C.supp := by
        change r.1.1 ∈ C.supp
        exact r.1.2
      obtain ⟨hyC, hReachLocal⟩ :=
        reachable_to_component_deleteVertex_of_component C c
          (x := rGlobal) (y := y.1) hrGlobalC hReachGlobal
      let yLocal : {w : C // w ≠ c} :=
        ⟨⟨y.1.1, hyC⟩, fun hyc => y.1.2 (congrArg Subtype.val hyc)⟩
      have hccLocal :
          (deleteVertex C.toSimpleGraph c).connectedComponentMk r =
            (deleteVertex C.toSimpleGraph c).connectedComponentMk yLocal :=
        SimpleGraph.ConnectedComponent.sound hReachLocal
      have hrEq : (deleteVertex C.toSimpleGraph c).connectedComponentMk r = D := by
        simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff D r).1 hrD
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff D yLocal).2
        (hccLocal.symm.trans hrEq)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

lemma odd_componentDeleteVertexComponentMap
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent) (c : C)
    (D : (deleteVertex C.toSimpleGraph c).ConnectedComponent)
    (hOdd : Odd D.supp.ncard) :
    Odd (componentDeleteVertexComponentMap G C c D).supp.ncard := by
  have hcard : D.supp.ncard =
      (componentDeleteVertexComponentMap G C c D).supp.ncard := by
    simpa [Nat.card_coe_set_eq] using
      Nat.card_congr (componentDeleteVertexGlobalSuppEquiv G C c D)
  rwa [← hcard]

lemma componentDeleteVertexComponentMap_ne_componentMapDeleteVertex_of_even_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hEven : Even C.supp.ncard) (c : C)
    (D : (deleteVertex C.toSimpleGraph c).ConnectedComponent)
    {K : G.ConnectedComponent} (hKodd : K ∈ G.oddComponents)
    (hvK : c.1 ∉ K.supp) :
    componentDeleteVertexComponentMap G C c D ≠ componentMapDeleteVertex G K hvK := by
  intro hEq
  let rD := D.nonempty_supp.some
  let rGlobal := componentDeleteVertexToGlobalHom G C c rD
  have hrNew : rGlobal ∈ (componentDeleteVertexComponentMap G C c D).supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (componentDeleteVertexComponentMap G C c D) rGlobal).2 (by
        simp [componentDeleteVertexComponentMap, rD, rGlobal])
  have hrKmap : rGlobal ∈ (componentMapDeleteVertex G K hvK).supp := by
    simpa [hEq] using hrNew
  let yK : (componentMapDeleteVertex G K hvK).supp := ⟨rGlobal, hrKmap⟩
  let eK := componentDeleteVertexSuppEquiv G K hvK
  have hrK : rD.1.1 ∈ K.supp := by
    have hval : (eK.symm yK).1 = rD.1.1 := rfl
    rw [← hval]
    exact (eK.symm yK).2
  have hrC : rD.1.1 ∈ C.supp := rD.1.2
  have hKC : K = C := SimpleGraph.ConnectedComponent.eq_of_common_vertex hrK hrC
  have hOddC : Odd C.supp.ncard := by
    simpa [hKC] using hKodd
  exact (Nat.not_even_iff_odd.2 hOddC) hEven

lemma oddComponents_ncard_lt_deleteVertex_of_even_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hEven : Even C.supp.ncard) (c : C) :
    G.oddComponents.ncard < (deleteVertex G c.1).oddComponents.ncard := by
  classical
  let hLocalNonempty :=
    oddComponents_deleteVertex_nonempty_of_even_component G C hEven c
  let D0 : (deleteVertex C.toSimpleGraph c).oddComponents :=
    ⟨hLocalNonempty.some, hLocalNonempty.some_mem⟩
  let F : Option G.oddComponents → (deleteVertex G c.1).oddComponents
    | none =>
        ⟨componentDeleteVertexComponentMap G C c D0.1,
          odd_componentDeleteVertexComponentMap G C c D0.1 D0.2⟩
    | some K =>
        ⟨componentMapDeleteVertex G K.1
            (oddComponents_not_mem_even_component_vertex G C hEven c K.2),
          odd_componentMapDeleteVertex_of_not_mem G K.1
            (oddComponents_not_mem_even_component_vertex G C hEven c K.2) K.2⟩
  have hF_inj : Function.Injective F := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some K =>
            exfalso
            exact componentDeleteVertexComponentMap_ne_componentMapDeleteVertex_of_even_component
              G C hEven c D0.1 K.2
              (oddComponents_not_mem_even_component_vertex G C hEven c K.2)
              (congrArg Subtype.val hab)
    | some K =>
        cases b with
        | none =>
            exfalso
            exact componentDeleteVertexComponentMap_ne_componentMapDeleteVertex_of_even_component
              G C hEven c D0.1 K.2
              (oddComponents_not_mem_even_component_vertex G C hEven c K.2)
              (congrArg Subtype.val hab).symm
        | some L =>
            have hKL : K.1 = L.1 :=
              componentMapDeleteVertex_eq_imp_eq G
                (oddComponents_not_mem_even_component_vertex G C hEven c K.2)
                (oddComponents_not_mem_even_component_vertex G C hEven c L.2)
                (congrArg Subtype.val hab)
            apply congrArg Option.some
            exact Subtype.ext hKL
  have hle :
      Nat.card (Option G.oddComponents) ≤
        Nat.card (deleteVertex G c.1).oddComponents :=
    Nat.card_le_card_of_injective F hF_inj
  have hopt : Nat.card (Option G.oddComponents) = G.oddComponents.ncard + 1 := by
    letI : Fintype G.oddComponents := Fintype.ofFinite G.oddComponents
    rw [Nat.card_eq_fintype_card, Fintype.card_option,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have htarget :
      Nat.card (deleteVertex G c.1).oddComponents =
        (deleteVertex G c.1).oddComponents.ncard := by
    rw [Nat.card_coe_set_eq]
  omega

lemma no_isPerfectMatching_of_odd_natCard (G : SimpleGraph V) [Finite V]
    (hOdd : Odd (Nat.card V)) :
    ∀ M : G.Subgraph, ¬ M.IsPerfectMatching := by
  classical
  intro M hM
  letI : Fintype V := Fintype.ofFinite V
  have hEven : Even (Nat.card V) := by
    simpa [Nat.card_eq_fintype_card] using hM.even_card
  exact (Nat.not_even_iff_odd.2 hOdd) hEven

lemma no_isPerfectMatching_of_odd_component
    (G : SimpleGraph V) [Finite V] (C : G.ConnectedComponent)
    (hOdd : Odd C.supp.ncard) :
    ∀ M : C.toSimpleGraph.Subgraph, ¬ M.IsPerfectMatching := by
  have hOddCard : Odd (Nat.card C) := by
    simpa [Nat.card_coe_set_eq] using hOdd
  exact no_isPerfectMatching_of_odd_natCard C.toSimpleGraph hOddCard

lemma deletedComponent_nonempty
    (G : SimpleGraph V) [Finite V] {S : Set V} (C : DeletedComponent G S) :
    Nonempty C :=
  ⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩

noncomputable def componentSuppEquivIso {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun x := ⟨φ x.1, by
    have hx : G.connectedComponentMk x.1 = C := by
      simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff C x.1).1 x.2
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff (φ.connectedComponentEquiv C)
      (φ x.1)).2 (by
        simpa [SimpleGraph.Iso.connectedComponentEquiv_apply] using
          (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
            (φ := φ) (C := C) (v := x.1)).2 hx)⟩
  invFun y := ⟨φ.symm y.1, by
    have hy : H.connectedComponentMk y.1 = φ.connectedComponentEquiv C := by
      simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff
        (φ.connectedComponentEquiv C) y.1).1 y.2
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C (φ.symm y.1)).2 (by
      apply (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (φ := φ) (C := C) (v := φ.symm y.1)).1
      simpa [SimpleGraph.Iso.connectedComponentEquiv_apply] using hy)⟩
  left_inv x := by
    apply Subtype.ext
    exact Equiv.left_inv φ.toEquiv x.1
  right_inv y := by
    apply Subtype.ext
    exact Equiv.right_inv φ.toEquiv y.1

lemma odd_supp_ncard_iff_iso {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (C : G.ConnectedComponent) :
    Odd C.supp.ncard ↔ Odd (φ.connectedComponentEquiv C).supp.ncard := by
  have hcard : C.supp.ncard = (φ.connectedComponentEquiv C).supp.ncard := by
    simpa [Nat.card_coe_set_eq] using Nat.card_congr (componentSuppEquivIso φ C)
  rw [hcard]

noncomputable def oddComponentsEquivIso {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} [Finite V] [Finite W]
    (φ : G ≃g H) :
    G.oddComponents ≃ H.oddComponents :=
  Equiv.subtypeEquiv φ.connectedComponentEquiv (fun C => odd_supp_ncard_iff_iso φ C)

lemma ncard_oddComponents_eq_of_iso {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W} [Finite V] [Finite W]
    (φ : G ≃g H) :
    G.oddComponents.ncard = H.oddComponents.ncard := by
  simpa [Nat.card_coe_set_eq] using Nat.card_congr (oddComponentsEquivIso φ)

/-- The two deleted-vertex models used in Chapter 2 and Mathlib are isomorphic. -/
noncomputable def deleteVertsTopIsoDeleteVertices
    (G : SimpleGraph V) (S : Set V) :
    ((⊤ : G.Subgraph).deleteVerts S).coe ≃g delete_vertices G S where
  toFun x := ⟨x.1, by simpa using x.2.2⟩
  invFun x := ⟨x.1, ⟨by trivial, x.2⟩⟩
  map_rel_iff' := by
    intro x y
    change G.Adj x.1 y.1 ↔ ((⊤ : G.Subgraph).deleteVerts S).Adj x.1 y.1
    rw [SimpleGraph.Subgraph.deleteVerts_adj]
    simp [x.2.2, y.2.2]

lemma oddComponents_ncard_deleteVertsTop_eq_delete_vertices
    (G : SimpleGraph V) [Finite V] (S : Set V) :
    ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard =
      (delete_vertices G S).oddComponents.ncard :=
  ncard_oddComponents_eq_of_iso (deleteVertsTopIsoDeleteVertices G S)

lemma not_isTutteViolator_iff_delete_vertices_oddComponents_le
    (G : SimpleGraph V) [Finite V] (S : Set V) :
    ¬ G.IsTutteViolator S ↔
      (delete_vertices G S).oddComponents.ncard ≤ S.ncard := by
  rw [SimpleGraph.IsTutteViolator]
  rw [oddComponents_ncard_deleteVertsTop_eq_delete_vertices G S]
  exact not_lt

lemma ncard_eq_of_tutteCondition_and_gallaiEdmondsSet
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (hTutte : TutteCondition G) (hS : GallaiEdmondsSet G S) :
    S.ncard = Nat.card (DeletedComponent G S) := by
  have hLower : S.ncard ≤ Nat.card (DeletedComponent G S) :=
    GallaiEdmondsAux.ncard_le_deletedComponent_card_of_matchable G hS.1
  have hOddEq : Nat.card (DeletedComponent G S) =
      (delete_vertices G S).oddComponents.ncard :=
    GallaiEdmondsAux.deletedComponent_card_eq_oddComponents_ncard_of_gallaiEdmondsSet G hS
  have hUpperOdd : (delete_vertices G S).oddComponents.ncard ≤ S.ncard :=
    (not_isTutteViolator_iff_delete_vertices_oddComponents_le G S).1 (hTutte S)
  have hUpper : Nat.card (DeletedComponent G S) ≤ S.ncard := by
    rw [hOddEq]
    exact hUpperOdd
  exact le_antisymm hLower hUpper

lemma exists_isPerfectMatching_of_tutteCondition_and_gallaiEdmondsSet
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (hTutte : TutteCondition G) (hS : GallaiEdmondsSet G S) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  GallaiEdmondsAux.exists_isPerfectMatching_of_gallaiEdmondsSet_ncard_eq hS
    (ncard_eq_of_tutteCondition_and_gallaiEdmondsSet hTutte hS)

lemma exists_delete_vertices_oddComponents_gt_of_no_isPerfectMatching
    (G : SimpleGraph V) [Finite V]
    (hNo : ∀ M : G.Subgraph, ¬ M.IsPerfectMatching) :
    ∃ S : Set V, S.ncard < (delete_vertices G S).oddComponents.ncard := by
  classical
  by_contra hnone
  have hTutte : TutteCondition G := by
    intro S
    have hle : (delete_vertices G S).oddComponents.ncard ≤ S.ncard := by
      exact not_lt.mp (fun hlt => hnone ⟨S, hlt⟩)
    exact (not_isTutteViolator_iff_delete_vertices_oddComponents_le G S).2 hle
  rcases (SimpleGraph.tutte (G := G)).2 hTutte with ⟨M, hM⟩
  exact hNo M hM

lemma nat_add_two_le_of_lt_and_same_odd {a r : ℕ}
    (hlt : a < r) (hsame : Odd r ↔ Odd a) :
    a + 2 ≤ r := by
  by_cases ha : Odd a
  · have hr : Odd r := hsame.mpr ha
    rcases ha with ⟨m, hm⟩
    rcases hr with ⟨n, hn⟩
    omega
  · have hea : Even a := Nat.not_odd_iff_even.mp ha
    have hnotOddR : ¬ Odd r := fun hr => ha (hsame.mp hr)
    have her : Even r := Nat.not_odd_iff_even.mp hnotOddR
    rcases hea with ⟨m, hm⟩
    rcases her with ⟨n, hn⟩
    omega

lemma odd_oddComponents_delete_vertices_iff_odd_ncard_of_even_card
    (G : SimpleGraph V) [Finite V] (hEven : Even (Nat.card V)) (S : Set V) :
    Odd (delete_vertices G S).oddComponents.ncard ↔ Odd S.ncard := by
  classical
  have hS_le : S.ncard ≤ Nat.card V := by
    have hle : S.ncard ≤ (Set.univ : Set V).ncard :=
      Set.ncard_le_ncard (by intro x _hx; simp)
    simpa [Set.ncard_univ] using hle
  have hcomp_card :
      Nat.card (Sᶜ : Set V) = Nat.card V - S.ncard := by
    rw [Nat.card_coe_set_eq, Set.ncard_compl S]
  have hpar :
      Odd (delete_vertices G S).oddComponents.ncard ↔
        Odd (Nat.card V - S.ncard) := by
    simpa [hcomp_card] using
      (SimpleGraph.odd_ncard_oddComponents (delete_vertices G S))
  constructor
  · intro hOddQ
    have hOddComp : Odd (Nat.card V - S.ncard) := hpar.mp hOddQ
    have hnotEvenS : ¬ Even S.ncard := by
      intro hEvenS
      have hEvenComp : Even (Nat.card V - S.ncard) :=
        (Nat.even_sub hS_le).2 ⟨fun _ => hEvenS, fun _ => hEven⟩
      exact (Nat.not_even_iff_odd.2 hOddComp) hEvenComp
    exact Nat.not_even_iff_odd.1 hnotEvenS
  · intro hOddS
    have hnotEvenComp : ¬ Even (Nat.card V - S.ncard) := by
      intro hEvenComp
      have hiff : Even (Nat.card V) ↔ Even S.ncard :=
        (Nat.even_sub hS_le).1 hEvenComp
      exact (Nat.not_even_iff_odd.2 hOddS) (hiff.1 hEven)
    exact hpar.mpr (Nat.not_even_iff_odd.1 hnotEvenComp)

lemma exists_delete_vertices_oddComponents_ge_add_two_of_even_no_isPerfectMatching
    (G : SimpleGraph V) [Finite V] (hEven : Even (Nat.card V))
    (hNo : ∀ M : G.Subgraph, ¬ M.IsPerfectMatching) :
    ∃ S : Set V, S.ncard + 2 ≤ (delete_vertices G S).oddComponents.ncard := by
  obtain ⟨S, hlt⟩ := exists_delete_vertices_oddComponents_gt_of_no_isPerfectMatching G hNo
  exact ⟨S, nat_add_two_le_of_lt_and_same_odd hlt
    (odd_oddComponents_delete_vertices_iff_odd_ncard_of_even_card G hEven S)⟩

/-- Components of `G - S` adjacent to a set of deleted vertices. -/
def componentNeighbors (G : SimpleGraph V) [Finite V] {S : Set V}
    (A : Set S) : Set (DeletedComponent G S) :=
  {C | ∃ s : S, s ∈ A ∧ ∃ x : C.supp, G.Adj s.1 x.1.1}

lemma matchableToDeletedComponents_iff_hall
    (G : SimpleGraph V) [Finite V] (S : Set V) :
    MatchableToDeletedComponents G S ↔
      ∀ A : Set S, A.ncard ≤ (componentNeighbors G A).ncard := by
  classical
  constructor
  · rintro ⟨f, hf_inj, hf_adj⟩ A
    let g : A → (componentNeighbors G A) := fun a =>
      ⟨f a.1, ⟨a.1, a.2, hf_adj a.1⟩⟩
    have hg_inj : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact hf_inj (congrArg Subtype.val hab)
    simpa [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective g hg_inj
  · intro hHall
    letI : Fintype (DeletedComponent G S) := Fintype.ofFinite (DeletedComponent G S)
    let t : S → Finset (DeletedComponent G S) := fun s =>
      ({C : DeletedComponent G S | ∃ x : C.supp, G.Adj s.1 x.1.1} : Set _).toFinset
    obtain ⟨f, hf_inj, hf_mem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp (by
        intro U
        have hA := hHall (U : Set S)
        rw [Set.ncard_coe_finset] at hA
        have hEqSet : ((U.biUnion t : Finset (DeletedComponent G S)) : Set _) =
            componentNeighbors G (U : Set S) := by
          ext C
          simp [t, componentNeighbors]
        have hCardEq :
            (U.biUnion t).card = (componentNeighbors G (U : Set S)).ncard := by
          rw [← Set.ncard_coe_finset, hEqSet]
        rw [hCardEq]
        exact hA)
    refine ⟨f, hf_inj, ?_⟩
    intro s
    have hs : f s ∈ t s := hf_mem s
    simpa [t] using hs

lemma exists_componentNeighbors_lt_of_not_matchable
    (G : SimpleGraph V) [Finite V] (S : Set V)
    (hNo : ¬ MatchableToDeletedComponents G S) :
    ∃ A : Set S, (componentNeighbors G A).ncard < A.ncard := by
  classical
  by_contra hnone
  apply hNo
  exact (matchableToDeletedComponents_iff_hall G S).2 fun A =>
    not_lt.mp (fun hlt => hnone ⟨A, hlt⟩)

/-- The image in the ambient vertex type of a set of vertices from a subtype. -/
def subtypeImageSet {S : Set V} (A : Set S) : Set V :=
  Subtype.val '' A

lemma subtypeImageSet_subset {S : Set V} (A : Set S) :
    subtypeImageSet A ⊆ S := by
  rintro v ⟨a, _ha, rfl⟩
  exact a.2

lemma ncard_subtypeImageSet [Finite V] {S : Set V} (A : Set S) :
    (subtypeImageSet A).ncard = A.ncard := by
  exact Set.ncard_image_of_injective A Subtype.val_injective

lemma ncard_diff_subtypeImageSet [Finite V] {S : Set V} (A : Set S) :
    (S \ subtypeImageSet A).ncard = S.ncard - A.ncard := by
  rw [Set.ncard_diff (subtypeImageSet_subset A), ncard_subtypeImageSet]

lemma ncard_union_singleton_of_not_mem [Finite V] {S : Set V} {v : V} (hv : v ∉ S) :
    (S ∪ {v}).ncard = S.ncard + 1 := by
  have hdis : Disjoint S ({v} : Set V) := by
    rw [Set.disjoint_singleton_right]
    exact hv
  rw [Set.ncard_union_eq hdis]
  simp

noncomputable def deleteVertexDeleteVerticesIso
    (G : SimpleGraph V) (S : Set V) (v : (Sᶜ : Set V)) :
    deleteVertex (delete_vertices G S) v ≃g delete_vertices G (S ∪ {v.1}) where
  toFun x := ⟨x.1.1, by
    intro hx
    rcases hx with hxS | hxv
    · exact x.1.2 hxS
    · exact x.2 (Subtype.ext (by simpa using hxv))⟩
  invFun x := ⟨⟨x.1, by
    intro hxS
    exact x.2 (Or.inl hxS)⟩, by
      intro hxv
      exact x.2 (Or.inr (by simpa using congrArg Subtype.val hxv))⟩
  map_rel_iff' := by
    intro x y
    change G.Adj x.1.1 y.1.1 ↔ (deleteVertex (delete_vertices G S) v).Adj x y
    rw [SimpleGraph.induce_adj]
    simp [deleteVertex, delete_vertices]

lemma oddComponents_ncard_deleteVertex_delete_vertices_eq_union_singleton
    (G : SimpleGraph V) [Finite V] (S : Set V) (v : (Sᶜ : Set V)) :
    (deleteVertex (delete_vertices G S) v).oddComponents.ncard =
      (delete_vertices G (S ∪ {v.1})).oddComponents.ncard :=
  ncard_oddComponents_eq_of_iso (deleteVertexDeleteVerticesIso G S v)

lemma defect_le_union_singleton_of_even_deleted_component
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (hEven : Even C.supp.ncard) (c : C) :
    defect G S ≤ defect G (S ∪ {c.1.1}) := by
  classical
  have hq_lt :
      (delete_vertices G S).oddComponents.ncard <
        (deleteVertex (delete_vertices G S) c.1).oddComponents.ncard :=
    oddComponents_ncard_lt_deleteVertex_of_even_component
      (delete_vertices G S) C hEven c
  have hq_eq :
      (deleteVertex (delete_vertices G S) c.1).oddComponents.ncard =
        (delete_vertices G (S ∪ {c.1.1})).oddComponents.ncard :=
    oddComponents_ncard_deleteVertex_delete_vertices_eq_union_singleton G S c.1
  have hq_succ :
      (delete_vertices G S).oddComponents.ncard + 1 ≤
        (delete_vertices G (S ∪ {c.1.1})).oddComponents.ncard := by
    omega
  have hcard :
      (S ∪ {c.1.1}).ncard = S.ncard + 1 :=
    ncard_union_singleton_of_not_mem c.1.2
  dsimp [defect]
  rw [hcard]
  omega

lemma all_components_odd_of_largest_max_defect
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hLargest : ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard) :
    ∀ C : DeletedComponent G S, C ∈ (delete_vertices G S).oddComponents := by
  classical
  intro C
  by_contra hnotOdd
  have hEven : Even C.supp.ncard := by
    exact Nat.not_odd_iff_even.1 (by
      intro hOdd
      exact hnotOdd (by simpa using hOdd))
  let c : C := ⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩
  let T : Set V := S ∪ {c.1.1}
  have hdef_le : defect G S ≤ defect G T := by
    simpa [T] using defect_le_union_singleton_of_even_deleted_component G C hEven c
  have hdef_ge : defect G T ≤ defect G S := hMax T
  have hdef_eq : defect G T = defect G S := le_antisymm hdef_ge hdef_le
  have hcard_le : T.ncard ≤ S.ncard := hLargest T hdef_eq
  have hcard : T.ncard = S.ncard + 1 := by
    simpa [T] using ncard_union_singleton_of_not_mem c.1.2
  omega

lemma no_isPerfectMatching_component_of_largest_max_defect
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hLargest : ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard)
    (C : DeletedComponent G S) :
    ∀ M : C.toSimpleGraph.Subgraph, ¬ M.IsPerfectMatching := by
  have hOdd : Odd C.supp.ncard := by
    simpa using all_components_odd_of_largest_max_defect G hMax hLargest C
  exact no_isPerfectMatching_of_odd_component (delete_vertices G S) C hOdd

lemma exists_local_tutte_surplus_of_no_deleteVertex_matching
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hLargest : ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard)
    (C : DeletedComponent G S) (c : C)
    (hNo : ∀ M : (deleteVertex C.toSimpleGraph c).Subgraph, ¬ M.IsPerfectMatching) :
    ∃ A : Set {w : C // w ≠ c},
      A.ncard + 2 ≤ (delete_vertices (deleteVertex C.toSimpleGraph c) A).oddComponents.ncard := by
  have hOddC : Odd C.supp.ncard := by
    simpa using all_components_odd_of_largest_max_defect G hMax hLargest C
  have hEvenDelete :
      Even (Nat.card {w : C // w ≠ c}) :=
    even_natCard_deleteVertex_of_odd_component (delete_vertices G S) C hOddC c
  exact exists_delete_vertices_oddComponents_ge_add_two_of_even_no_isPerfectMatching
    (deleteVertex C.toSimpleGraph c) hEvenDelete hNo

/-- The ambient vertices represented by a set inside `C - c`. -/
def localDeleteComponentImageSet
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) : Set V :=
  (fun a : {w : C // w ≠ c} => a.1.1.1) '' A

/-- The ambient deletion set obtained from a local obstruction `A ⊆ C - c`. -/
def localLiftSet
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) : Set V :=
  S ∪ {c.1.1} ∪ localDeleteComponentImageSet C c A

lemma localDeleteComponentImageSet_subset_compl
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) :
    localDeleteComponentImageSet C c A ⊆ Sᶜ := by
  rintro v ⟨a, _ha, rfl⟩
  exact a.1.1.2

lemma localDeleteComponentImageSet_not_mem_deleted_vertex
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) :
    c.1.1 ∉ localDeleteComponentImageSet C c A := by
  rintro ⟨a, _ha, ha⟩
  exact a.2 (by
    apply Subtype.ext
    apply Subtype.ext
    exact ha)

lemma localDeleteComponentImageSet_injective
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C) :
    Function.Injective (fun a : {w : C // w ≠ c} => a.1.1.1) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hab

lemma ncard_localDeleteComponentImageSet
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (C : DeletedComponent G S) (c : C) (A : Set {w : C // w ≠ c}) :
    (localDeleteComponentImageSet C c A).ncard = A.ncard := by
  exact Set.ncard_image_of_injective A (localDeleteComponentImageSet_injective C c)

lemma ncard_deleted_union_singleton_union_localImage
    {G : SimpleGraph V} [Finite V] {S : Set V}
    (C : DeletedComponent G S) (c : C) (A : Set {w : C // w ≠ c}) :
    (localLiftSet C c A).ncard =
      S.ncard + 1 + A.ncard := by
  classical
  let I := localDeleteComponentImageSet C c A
  have hS_single : Disjoint S ({c.1.1} : Set V) := by
    rw [Set.disjoint_singleton_right]
    exact c.1.2
  have hS_I : Disjoint S I := by
    rw [Set.disjoint_left]
    intro v hvS hvI
    exact (localDeleteComponentImageSet_subset_compl C c A hvI) hvS
  have hsingle_I : Disjoint ({c.1.1} : Set V) I := by
    rw [Set.disjoint_singleton_left]
    exact localDeleteComponentImageSet_not_mem_deleted_vertex C c A
  have hSI : Disjoint (S ∪ {c.1.1}) I := by
    rw [Set.disjoint_union_left]
    exact ⟨hS_I, hsingle_I⟩
  have hIcard : I.ncard = A.ncard := by
    simpa [I] using ncard_localDeleteComponentImageSet C c A
  dsimp [localLiftSet]
  rw [Set.ncard_union_eq hSI, Set.ncard_union_eq hS_single, hIcard]
  simp

def localDeleteComponentHomToGlobal
    (G : SimpleGraph V) {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) :
    delete_vertices (deleteVertex C.toSimpleGraph c) A →g
      delete_vertices G (localLiftSet C c A) where
  toFun x := ⟨x.1.1.1, by
    intro hxT
    rcases hxT with hxBase | hxA
    rcases hxBase with hxS | hxC
    · exact x.1.1.1.2 hxS
    · exact x.1.2 (by
        apply Subtype.ext
        apply Subtype.ext
        exact hxC)
    · rcases hxA with ⟨a, haA, hax⟩
      have hEq : a = x.1 := localDeleteComponentImageSet_injective C c hax
      exact x.2 (by simpa [hEq] using haA)⟩
  map_rel' := by
    intro x y hxy
    change G.Adj x.1.1.1 y.1.1.1
    simpa [delete_vertices, deleteVertex, SimpleGraph.ConnectedComponent.toSimpleGraph] using hxy

lemma localLiftSet_subset_superset
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) :
    S ⊆ localLiftSet C c A := by
  intro v hv
  exact Or.inl (Or.inl hv)

lemma localLiftSet_vertex_not_mem_S
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) {x : V}
    (hx : x ∉ localLiftSet C c A) :
    x ∉ S := by
  intro hxS
  exact hx (Or.inl (Or.inl hxS))

lemma localLiftSet_vertex_ne_c
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) {x : V}
    (hx : x ∉ localLiftSet C c A) :
    x ≠ c.1.1 := by
  intro hxc
  exact hx (Or.inl (Or.inr (by simpa [hxc])))

lemma localLiftSet_vertex_not_mem_image
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c}) {x : V}
    (hx : x ∉ localLiftSet C c A) :
    x ∉ localDeleteComponentImageSet C c A := by
  intro hxI
  exact hx (Or.inr hxI)

def globalLiftVertexToLocal
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c})
    (x : ((localLiftSet C c A)ᶜ : Set V))
    (hxC : (⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩ : (Sᶜ : Set V)) ∈ C.supp) :
    (Aᶜ : Set {w : C // w ≠ c}) :=
  ⟨⟨⟨⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩, hxC⟩,
      fun hxc => localLiftSet_vertex_ne_c C c A x.2
        (congrArg (fun z : C => z.1.1) hxc)⟩,
    by
      intro hxA
      exact localLiftSet_vertex_not_mem_image C c A x.2
        ⟨⟨⟨⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩, hxC⟩,
            fun hxc => localLiftSet_vertex_ne_c C c A x.2
              (congrArg (fun z : C => z.1.1) hxc)⟩, hxA, rfl⟩⟩

lemma reachable_to_local_deleteComponent_of_global_lift
    {G : SimpleGraph V} {S : Set V} (C : DeletedComponent G S) (c : C)
    (A : Set {w : C // w ≠ c})
    {x y : ((localLiftSet C c A)ᶜ : Set V)}
    (hxC : (⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩ : (Sᶜ : Set V)) ∈ C.supp)
    (hxy : (delete_vertices G (localLiftSet C c A)).Reachable x y) :
    ∃ hyC : (⟨y.1, localLiftSet_vertex_not_mem_S C c A y.2⟩ : (Sᶜ : Set V)) ∈ C.supp,
      (delete_vertices (deleteVertex C.toSimpleGraph c) A).Reachable
        ⟨⟨⟨⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩, hxC⟩,
            fun hxc => localLiftSet_vertex_ne_c C c A x.2
              (congrArg (fun z : C => z.1.1) hxc)⟩,
          by
            intro hxA
            exact localLiftSet_vertex_not_mem_image C c A x.2
              ⟨⟨⟨⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩, hxC⟩,
                  fun hxc => localLiftSet_vertex_ne_c C c A x.2
                    (congrArg (fun z : C => z.1.1) hxc)⟩, hxA, rfl⟩⟩
        ⟨⟨⟨⟨y.1, localLiftSet_vertex_not_mem_S C c A y.2⟩, hyC⟩,
            fun hyc => localLiftSet_vertex_ne_c C c A y.2
              (congrArg (fun z : C => z.1.1) hyc)⟩,
          by
            intro hyA
            exact localLiftSet_vertex_not_mem_image C c A y.2
              ⟨⟨⟨⟨y.1, localLiftSet_vertex_not_mem_S C c A y.2⟩, hyC⟩,
                  fun hyc => localLiftSet_vertex_ne_c C c A y.2
                    (congrArg (fun z : C => z.1.1) hyc)⟩, hyA, rfl⟩⟩ := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil =>
      exact ⟨hxC, SimpleGraph.Walk.nil.reachable⟩
  | cons hxy p ih =>
      rename_i x z y
      have hxzG : G.Adj x.1 z.1 := by
        simpa [delete_vertices] using hxy
      have hzC : (⟨z.1, localLiftSet_vertex_not_mem_S C c A z.2⟩ : (Sᶜ : Set V)) ∈
          C.supp := by
        have hxzS : (delete_vertices G S).Adj
            (⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩ : (Sᶜ : Set V))
            (⟨z.1, localLiftSet_vertex_not_mem_S C c A z.2⟩ : (Sᶜ : Set V)) := by
          simpa [delete_vertices] using hxzG
        exact C.mem_supp_of_adj_mem_supp hxC hxzS
      obtain ⟨hyC, hReachLocal⟩ := ih hzC
      obtain ⟨pLocal⟩ := hReachLocal
      let xLocal : (Aᶜ : Set {w : C // w ≠ c}) :=
        ⟨⟨⟨⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩, hxC⟩,
            fun hxc => localLiftSet_vertex_ne_c C c A x.2
              (congrArg (fun z : C => z.1.1) hxc)⟩,
          by
            intro hxA
            exact localLiftSet_vertex_not_mem_image C c A x.2
              ⟨⟨⟨⟨x.1, localLiftSet_vertex_not_mem_S C c A x.2⟩, hxC⟩,
                  fun hxc => localLiftSet_vertex_ne_c C c A x.2
                    (congrArg (fun z : C => z.1.1) hxc)⟩, hxA, rfl⟩⟩
      let zLocal : (Aᶜ : Set {w : C // w ≠ c}) :=
        ⟨⟨⟨⟨z.1, localLiftSet_vertex_not_mem_S C c A z.2⟩, hzC⟩,
            fun hzc => localLiftSet_vertex_ne_c C c A z.2
              (congrArg (fun z : C => z.1.1) hzc)⟩,
          by
            intro hzA
            exact localLiftSet_vertex_not_mem_image C c A z.2
              ⟨⟨⟨⟨z.1, localLiftSet_vertex_not_mem_S C c A z.2⟩, hzC⟩,
                  fun hzc => localLiftSet_vertex_ne_c C c A z.2
                    (congrArg (fun z : C => z.1.1) hzc)⟩, hzA, rfl⟩⟩
      have hxzLocal :
          (delete_vertices (deleteVertex C.toSimpleGraph c) A).Adj xLocal zLocal := by
        change (deleteVertex C.toSimpleGraph c).Adj xLocal.1 zLocal.1
        change C.toSimpleGraph.Adj xLocal.1.1 zLocal.1.1
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph, xLocal, zLocal] using hxzG
      exact ⟨hyC, (SimpleGraph.Walk.cons hxzLocal pLocal).reachable⟩

noncomputable def localDeleteComponentMapToGlobal
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (c : C) (A : Set {w : C // w ≠ c})
    (D : (delete_vertices (deleteVertex C.toSimpleGraph c) A).ConnectedComponent) :
    (delete_vertices G (localLiftSet C c A)).ConnectedComponent :=
  let r := D.nonempty_supp.some
  (delete_vertices G (localLiftSet C c A)).connectedComponentMk
    (localDeleteComponentHomToGlobal G C c A r)

noncomputable def localDeleteComponentGlobalSuppEquiv
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (c : C) (A : Set {w : C // w ≠ c})
    (D : (delete_vertices (deleteVertex C.toSimpleGraph c) A).ConnectedComponent) :
    D.supp ≃ (localDeleteComponentMapToGlobal G C c A D).supp where
  toFun x := by
    let r := D.nonempty_supp.some
    have hxD : x.1 ∈ D.supp := x.2
    have hrD : r ∈ D.supp := D.nonempty_supp.some_mem
    have hcc : (delete_vertices (deleteVertex C.toSimpleGraph c) A).connectedComponentMk x.1 =
        (delete_vertices (deleteVertex C.toSimpleGraph c) A).connectedComponentMk r := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxD hrD
      rw [hxD, hrD]
    exact ⟨localDeleteComponentHomToGlobal G C c A x.1, by
      have hReach := SimpleGraph.ConnectedComponent.exact hcc
      have hReachGlobal : (delete_vertices G (localLiftSet C c A)).Reachable
          (localDeleteComponentHomToGlobal G C c A x.1)
          (localDeleteComponentHomToGlobal G C c A r) :=
        hReach.map (localDeleteComponentHomToGlobal G C c A)
      have hccGlobal :
          (delete_vertices G (localLiftSet C c A)).connectedComponentMk
              (localDeleteComponentHomToGlobal G C c A x.1) =
            (delete_vertices G (localLiftSet C c A)).connectedComponentMk
              (localDeleteComponentHomToGlobal G C c A r) :=
        SimpleGraph.ConnectedComponent.sound hReachGlobal
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (localDeleteComponentMapToGlobal G C c A D)
        (localDeleteComponentHomToGlobal G C c A x.1)).2
        (by simpa [localDeleteComponentMapToGlobal, r] using hccGlobal)⟩
  invFun y := by
    let r := D.nonempty_supp.some
    let rGlobal := localDeleteComponentHomToGlobal G C c A r
    have hrD : r ∈ D.supp := D.nonempty_supp.some_mem
    have hrC :
        (⟨rGlobal.1, localLiftSet_vertex_not_mem_S C c A rGlobal.2⟩ : (Sᶜ : Set V)) ∈
          C.supp := by
      change r.1.1.1 ∈ C.supp
      exact r.1.1.2
    have hycc :
        (delete_vertices G (localLiftSet C c A)).connectedComponentMk y.1 =
          localDeleteComponentMapToGlobal G C c A D := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (localDeleteComponentMapToGlobal G C c A D) y.1).1 y.2
    have hccGlobal :
        (delete_vertices G (localLiftSet C c A)).connectedComponentMk rGlobal =
          (delete_vertices G (localLiftSet C c A)).connectedComponentMk y.1 := by
      simpa [localDeleteComponentMapToGlobal, r, rGlobal] using hycc.symm
    have hReachGlobal := SimpleGraph.ConnectedComponent.exact hccGlobal
    let hres :=
      reachable_to_local_deleteComponent_of_global_lift C c A
        (x := rGlobal) (y := y.1) hrC hReachGlobal
    let hyC := Classical.choose hres
    let hReachLocal := Classical.choose_spec hres
    let yLocal := globalLiftVertexToLocal C c A y.1 hyC
    refine ⟨yLocal, ?_⟩
    have hroot :
        globalLiftVertexToLocal C c A rGlobal hrC = r := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have hccLocal :
        (delete_vertices (deleteVertex C.toSimpleGraph c) A).connectedComponentMk r =
          (delete_vertices (deleteVertex C.toSimpleGraph c) A).connectedComponentMk yLocal := by
      have hcc :=
        SimpleGraph.ConnectedComponent.sound hReachLocal
      simpa [globalLiftVertexToLocal, yLocal, hroot] using hcc
    have hrEq : (delete_vertices (deleteVertex C.toSimpleGraph c) A).connectedComponentMk r = D := by
      simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff D r).1 hrD
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff D yLocal).2
      (hccLocal.symm.trans hrEq)
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

lemma odd_localDeleteComponentMapToGlobal
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (c : C) (A : Set {w : C // w ≠ c})
    (D : (delete_vertices (deleteVertex C.toSimpleGraph c) A).ConnectedComponent)
    (hOdd : Odd D.supp.ncard) :
    Odd (localDeleteComponentMapToGlobal G C c A D).supp.ncard := by
  have hcard : D.supp.ncard =
      (localDeleteComponentMapToGlobal G C c A D).supp.ncard := by
    simpa [Nat.card_coe_set_eq] using
      Nat.card_congr (localDeleteComponentGlobalSuppEquiv G C c A D)
  rwa [← hcard]

lemma oldComponent_vertex_ne_deleted_vertex
    {G : SimpleGraph V} [Finite V] {S : Set V}
    {C D : DeletedComponent G S} (hDne : D ≠ C) (c : C)
    (x : D.supp) :
    x.1.1 ≠ c.1.1 := by
  intro hxc
  have hcD : c.1 ∈ D.supp := by
    have hx_eq : x.1 = c.1 := Subtype.ext hxc
    simpa [← hx_eq] using x.2
  exact hDne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hcD c.2)

lemma oldComponent_vertex_not_mem_localImage
    {G : SimpleGraph V} [Finite V] {S : Set V}
    {C D : DeletedComponent G S} (hDne : D ≠ C) (c : C)
    (A : Set {w : C // w ≠ c}) (x : D.supp) :
    x.1.1 ∉ localDeleteComponentImageSet C c A := by
  rintro ⟨a, _ha, hax⟩
  have hxC : x.1 ∈ C.supp := by
    have hx_eq : x.1 = a.1.1 := Subtype.ext hax.symm
    simpa [hx_eq] using a.1.1.2
  exact hDne (SimpleGraph.ConnectedComponent.eq_of_common_vertex x.2 hxC)

lemma oldComponent_vertex_not_mem_localLiftSet
    {G : SimpleGraph V} [Finite V] {S : Set V}
    {C D : DeletedComponent G S} (hDne : D ≠ C) (c : C)
    (A : Set {w : C // w ≠ c}) (x : D.supp) :
    x.1.1 ∉ localLiftSet C c A := by
  intro hxT
  rcases hxT with hxBase | hxA
  · rcases hxBase with hxS | hxc
    · exact x.1.2 hxS
    · exact oldComponent_vertex_ne_deleted_vertex hDne c x hxc
  · exact oldComponent_vertex_not_mem_localImage hDne c A x hxA

lemma reachable_to_global_lift_of_old_component
    {G : SimpleGraph V} [Finite V] {S : Set V}
    {C D : DeletedComponent G S} (hDne : D ≠ C) (c : C)
    (A : Set {w : C // w ≠ c})
    {x y : (Sᶜ : Set V)}
    (hxD : x ∈ D.supp) (hxy : (delete_vertices G S).Reachable x y) :
    ∃ hyT : y.1 ∉ localLiftSet C c A,
      (delete_vertices G (localLiftSet C c A)).Reachable
        ⟨x.1, oldComponent_vertex_not_mem_localLiftSet hDne c A ⟨x, hxD⟩⟩
        ⟨y.1, hyT⟩ := by
  obtain ⟨p⟩ := hxy
  revert hxD
  induction p with
  | nil =>
      rename_i u
      intro hxD
      exact ⟨oldComponent_vertex_not_mem_localLiftSet hDne c A ⟨u, hxD⟩,
        SimpleGraph.Walk.nil.reachable⟩
  | cons hxy p ih =>
      intro hxD
      rename_i x z y
      have hxzG : G.Adj x.1 z.1 := by
        simpa [delete_vertices] using hxy
      have hzD : z ∈ D.supp := D.mem_supp_of_adj_mem_supp hxD hxy
      obtain ⟨hyT, hReach⟩ := ih hzD
      obtain ⟨pT⟩ := hReach
      let xT : ((localLiftSet C c A)ᶜ : Set V) :=
        ⟨x.1, oldComponent_vertex_not_mem_localLiftSet hDne c A ⟨x, hxD⟩⟩
      let zT : ((localLiftSet C c A)ᶜ : Set V) :=
        ⟨z.1, oldComponent_vertex_not_mem_localLiftSet hDne c A ⟨z, hzD⟩⟩
      have hxzT : (delete_vertices G (localLiftSet C c A)).Adj xT zT := by
        simpa [delete_vertices, xT, zT] using hxzG
      exact ⟨hyT, (SimpleGraph.Walk.cons hxzT pT).reachable⟩

def deleteVerticesHomOfSuperset
    (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) :
    delete_vertices G T →g delete_vertices G S where
  toFun x := ⟨x.1, fun hxS => x.2 (hST hxS)⟩
  map_rel' := by
    intro x y hxy
    simpa [delete_vertices] using hxy

noncomputable def oldComponentMapToGlobal
    (G : SimpleGraph V) [Finite V] {S : Set V}
    {C : DeletedComponent G S} (c : C) (A : Set {w : C // w ≠ c})
    (D : DeletedComponent G S) (hDne : D ≠ C) :
    (delete_vertices G (localLiftSet C c A)).ConnectedComponent :=
  let r := D.nonempty_supp.some
  (delete_vertices G (localLiftSet C c A)).connectedComponentMk
    ⟨r.1, oldComponent_vertex_not_mem_localLiftSet hDne c A
      ⟨r, D.nonempty_supp.some_mem⟩⟩

noncomputable def oldComponentGlobalSuppEquiv
    (G : SimpleGraph V) [Finite V] {S : Set V}
    {C : DeletedComponent G S} (c : C) (A : Set {w : C // w ≠ c})
    (D : DeletedComponent G S) (hDne : D ≠ C) :
    D.supp ≃ (oldComponentMapToGlobal G c A D hDne).supp where
  toFun x := by
    let xT : ((localLiftSet C c A)ᶜ : Set V) :=
      ⟨x.1.1, oldComponent_vertex_not_mem_localLiftSet hDne c A x⟩
    refine ⟨xT, ?_⟩
    let r := D.nonempty_supp.some
    let rT : ((localLiftSet C c A)ᶜ : Set V) :=
      ⟨r.1, oldComponent_vertex_not_mem_localLiftSet hDne c A
        ⟨r, D.nonempty_supp.some_mem⟩⟩
    have hxD : x.1 ∈ D.supp := x.2
    have hrD : r ∈ D.supp := D.nonempty_supp.some_mem
    have hcc : (delete_vertices G S).connectedComponentMk x.1 =
        (delete_vertices G S).connectedComponentMk r := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxD hrD
      rw [hxD, hrD]
    have hReach := SimpleGraph.ConnectedComponent.exact hcc
    obtain ⟨_hrT, hReachT⟩ :=
      reachable_to_global_lift_of_old_component hDne c A x.2 hReach
    have hccT :
        (delete_vertices G (localLiftSet C c A)).connectedComponentMk xT =
          (delete_vertices G (localLiftSet C c A)).connectedComponentMk rT := by
      have hroot : (⟨r.1, _hrT⟩ : ((localLiftSet C c A)ᶜ : Set V)) = rT := by
        apply Subtype.ext
        rfl
      simpa [xT, rT, hroot] using SimpleGraph.ConnectedComponent.sound hReachT
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (oldComponentMapToGlobal G c A D hDne) xT).2
      (by simpa [oldComponentMapToGlobal, r, rT] using hccT)
  invFun y := by
    let r := D.nonempty_supp.some
    let rT : ((localLiftSet C c A)ᶜ : Set V) :=
      ⟨r.1, oldComponent_vertex_not_mem_localLiftSet hDne c A
        ⟨r, D.nonempty_supp.some_mem⟩⟩
    have hrD : r ∈ D.supp := D.nonempty_supp.some_mem
    have hycc :
        (delete_vertices G (localLiftSet C c A)).connectedComponentMk y.1 =
          oldComponentMapToGlobal G c A D hDne := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (oldComponentMapToGlobal G c A D hDne) y.1).1 y.2
    have hccT :
        (delete_vertices G (localLiftSet C c A)).connectedComponentMk rT =
          (delete_vertices G (localLiftSet C c A)).connectedComponentMk y.1 := by
      simpa [oldComponentMapToGlobal, r, rT] using hycc.symm
    exact ⟨⟨y.1.1, localLiftSet_vertex_not_mem_S C c A y.1.2⟩, by
      let hST : S ⊆ localLiftSet C c A := localLiftSet_subset_superset C c A
      obtain ⟨pT⟩ := SimpleGraph.ConnectedComponent.exact hccT
      have pS : (delete_vertices G S).Walk
          ⟨rT.1, fun hxS => rT.2 (hST hxS)⟩
          ⟨y.1.1, localLiftSet_vertex_not_mem_S C c A y.1.2⟩ :=
        pT.map (deleteVerticesHomOfSuperset G hST)
      have hccS :
          (delete_vertices G S).connectedComponentMk
              ⟨rT.1, fun hxS => rT.2 (hST hxS)⟩ =
            (delete_vertices G S).connectedComponentMk
              ⟨y.1.1, localLiftSet_vertex_not_mem_S C c A y.1.2⟩ :=
        SimpleGraph.ConnectedComponent.sound pS.reachable
      have hroot : (⟨rT.1, fun hxS => rT.2 (hST hxS)⟩ : (Sᶜ : Set V)) = r := by
        apply Subtype.ext
        rfl
      have hrEq : (delete_vertices G S).connectedComponentMk r = D := by
        simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff D r).1 hrD
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      simpa [hroot] using hccS.symm.trans hrEq⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

lemma odd_oldComponentMapToGlobal
    (G : SimpleGraph V) [Finite V] {S : Set V}
    {C : DeletedComponent G S} (c : C) (A : Set {w : C // w ≠ c})
    (D : DeletedComponent G S) (hDne : D ≠ C)
    (hOdd : Odd D.supp.ncard) :
    Odd (oldComponentMapToGlobal G c A D hDne).supp.ncard := by
  have hcard : D.supp.ncard =
      (oldComponentMapToGlobal G c A D hDne).supp.ncard := by
    simpa [Nat.card_coe_set_eq] using
      Nat.card_congr (oldComponentGlobalSuppEquiv G c A D hDne)
  rwa [← hcard]

lemma localDeleteComponentMapToGlobal_eq_imp_eq
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (c : C) (A : Set {w : C // w ≠ c})
    {D E : (delete_vertices (deleteVertex C.toSimpleGraph c) A).ConnectedComponent}
    (hEq : localDeleteComponentMapToGlobal G C c A D =
      localDeleteComponentMapToGlobal G C c A E) :
    D = E := by
  let rD := D.nonempty_supp.some
  let rG := localDeleteComponentHomToGlobal G C c A rD
  have hrD : rD ∈ D.supp := D.nonempty_supp.some_mem
  have hrDmap : rG ∈ (localDeleteComponentMapToGlobal G C c A D).supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (localDeleteComponentMapToGlobal G C c A D) rG).2 (by
        simp [localDeleteComponentMapToGlobal, rD, rG])
  have hrEmap : rG ∈ (localDeleteComponentMapToGlobal G C c A E).supp := by
    simpa [hEq] using hrDmap
  let yE : (localDeleteComponentMapToGlobal G C c A E).supp := ⟨rG, hrEmap⟩
  let eE := localDeleteComponentGlobalSuppEquiv G C c A E
  have hrE : rD ∈ E.supp := by
    have hval : (eE.symm yE).1 = rD := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [← hval]
    exact (eE.symm yE).2
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hrD hrE

lemma oldComponentMapToGlobal_eq_imp_eq
    (G : SimpleGraph V) [Finite V] {S : Set V}
    {C : DeletedComponent G S} (c : C) (A : Set {w : C // w ≠ c})
    {D E : DeletedComponent G S} (hDne : D ≠ C) (hEne : E ≠ C)
    (hEq : oldComponentMapToGlobal G c A D hDne =
      oldComponentMapToGlobal G c A E hEne) :
    D = E := by
  let rD := D.nonempty_supp.some
  let rG : ((localLiftSet C c A)ᶜ : Set V) :=
    ⟨rD.1, oldComponent_vertex_not_mem_localLiftSet hDne c A
      ⟨rD, D.nonempty_supp.some_mem⟩⟩
  have hrD : rD ∈ D.supp := D.nonempty_supp.some_mem
  have hrDmap : rG ∈ (oldComponentMapToGlobal G c A D hDne).supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (oldComponentMapToGlobal G c A D hDne) rG).2 (by
        simp [oldComponentMapToGlobal, rD, rG])
  have hrEmap : rG ∈ (oldComponentMapToGlobal G c A E hEne).supp := by
    simpa [hEq] using hrDmap
  let yE : (oldComponentMapToGlobal G c A E hEne).supp := ⟨rG, hrEmap⟩
  let eE := oldComponentGlobalSuppEquiv G c A E hEne
  have hrE : rD ∈ E.supp := by
    have hval : (eE.symm yE).1 = rD := by
      apply Subtype.ext
      rfl
    rw [← hval]
    exact (eE.symm yE).2
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hrD hrE

lemma oldComponentMapToGlobal_ne_localDeleteComponentMapToGlobal
    (G : SimpleGraph V) [Finite V] {S : Set V}
    {C : DeletedComponent G S} (c : C) (A : Set {w : C // w ≠ c})
    {D : DeletedComponent G S} (hDne : D ≠ C)
    (E : (delete_vertices (deleteVertex C.toSimpleGraph c) A).ConnectedComponent) :
    oldComponentMapToGlobal G c A D hDne ≠
      localDeleteComponentMapToGlobal G C c A E := by
  intro hEq
  let rD := D.nonempty_supp.some
  let rG : ((localLiftSet C c A)ᶜ : Set V) :=
    ⟨rD.1, oldComponent_vertex_not_mem_localLiftSet hDne c A
      ⟨rD, D.nonempty_supp.some_mem⟩⟩
  have hrD : rD ∈ D.supp := D.nonempty_supp.some_mem
  have hrDmap : rG ∈ (oldComponentMapToGlobal G c A D hDne).supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (oldComponentMapToGlobal G c A D hDne) rG).2 (by
        simp [oldComponentMapToGlobal, rD, rG])
  have hrEmap : rG ∈ (localDeleteComponentMapToGlobal G C c A E).supp := by
    simpa [hEq] using hrDmap
  let yE : (localDeleteComponentMapToGlobal G C c A E).supp := ⟨rG, hrEmap⟩
  let eE := localDeleteComponentGlobalSuppEquiv G C c A E
  have hrC : rD ∈ C.supp := by
    have hval : (eE.symm yE).1.1.1 = rD := by
      apply Subtype.ext
      rfl
    rw [← hval]
    exact (eE.symm yE).1.1.1.2
  exact hDne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hrD hrC)

lemma oddComponents_ncard_lift_lower_bound
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (hCodd : C ∈ (delete_vertices G S).oddComponents)
    (c : C) (A : Set {w : C // w ≠ c}) :
    (delete_vertices G S).oddComponents.ncard - 1 +
        (delete_vertices (deleteVertex C.toSimpleGraph c) A).oddComponents.ncard ≤
      (delete_vertices G (localLiftSet C c A)).oddComponents.ncard := by
  classical
  let oldSet : Set (DeletedComponent G S) :=
    {D | D ∈ (delete_vertices G S).oddComponents ∧ D ≠ C}
  let localOdd : Set (delete_vertices (deleteVertex C.toSimpleGraph c) A).ConnectedComponent :=
    (delete_vertices (deleteVertex C.toSimpleGraph c) A).oddComponents
  let target : Set (delete_vertices G (localLiftSet C c A)).ConnectedComponent :=
    (delete_vertices G (localLiftSet C c A)).oddComponents
  let F : oldSet ⊕ localOdd → target
    | Sum.inl D =>
        ⟨oldComponentMapToGlobal G c A D.1 D.2.2,
          odd_oldComponentMapToGlobal G c A D.1 D.2.2 D.2.1⟩
    | Sum.inr D =>
        ⟨localDeleteComponentMapToGlobal G C c A D.1,
          odd_localDeleteComponentMapToGlobal G C c A D.1 D.2⟩
  have hF_inj : Function.Injective F := by
    intro X Y hXY
    cases X with
    | inl D =>
        cases Y with
        | inl E =>
            have hDE : D.1 = E.1 :=
              oldComponentMapToGlobal_eq_imp_eq G c A D.2.2 E.2.2
                (congrArg Subtype.val hXY)
            apply congrArg Sum.inl
            exact Subtype.ext hDE
        | inr E =>
            exfalso
            exact oldComponentMapToGlobal_ne_localDeleteComponentMapToGlobal
              G c A D.2.2 E.1 (congrArg Subtype.val hXY)
    | inr D =>
        cases Y with
        | inl E =>
            exfalso
            exact oldComponentMapToGlobal_ne_localDeleteComponentMapToGlobal
              G c A E.2.2 D.1 (congrArg Subtype.val hXY).symm
        | inr E =>
            have hDE : D.1 = E.1 :=
              localDeleteComponentMapToGlobal_eq_imp_eq G C c A
                (congrArg Subtype.val hXY)
            apply congrArg Sum.inr
            exact Subtype.ext hDE
  have hle_card : Nat.card (oldSet ⊕ localOdd) ≤ Nat.card target :=
    Nat.card_le_card_of_injective F hF_inj
  have hsource :
      Nat.card (oldSet ⊕ localOdd) = oldSet.ncard + localOdd.ncard := by
    rw [Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have htarget :
      Nat.card target = (delete_vertices G (localLiftSet C c A)).oddComponents.ncard := by
    rw [Nat.card_coe_set_eq]
  have hold_card :
      oldSet.ncard = (delete_vertices G S).oddComponents.ncard - 1 := by
    have hEq : oldSet = (delete_vertices G S).oddComponents \ {C} := by
      ext D
      simp [oldSet]
    have hsingleton :
        ({C} : Set (DeletedComponent G S)) ⊆ (delete_vertices G S).oddComponents := by
      intro D hD
      simpa [Set.mem_singleton_iff.mp hD] using hCodd
    rw [hEq, Set.ncard_diff hsingleton, Set.ncard_singleton]
  have hlocal_card :
      localOdd.ncard =
        (delete_vertices (deleteVertex C.toSimpleGraph c) A).oddComponents.ncard := by
    rfl
  omega

lemma defect_le_localLiftSet_of_local_surplus
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (C : DeletedComponent G S) (hCodd : C ∈ (delete_vertices G S).oddComponents)
    (c : C) (A : Set {w : C // w ≠ c})
    (hSurplus :
      A.ncard + 2 ≤ (delete_vertices (deleteVertex C.toSimpleGraph c) A).oddComponents.ncard) :
    defect G S ≤ defect G (localLiftSet C c A) := by
  classical
  have hLower :=
    oddComponents_ncard_lift_lower_bound G C hCodd c A
  have hcard :
      (localLiftSet C c A).ncard = S.ncard + 1 + A.ncard :=
    ncard_deleted_union_singleton_union_localImage C c A
  have hq_pos : 1 ≤ (delete_vertices G S).oddComponents.ncard := by
    have hpos : 0 < (delete_vertices G S).oddComponents.ncard :=
      (Set.ncard_pos (s := (delete_vertices G S).oddComponents)).2 ⟨C, hCodd⟩
    omega
  dsimp [defect]
  rw [hcard]
  omega

lemma factorCritical_component_of_largest_max_defect
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hLargest : ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard)
    (C : DeletedComponent G S) :
    IsFactorCritical C.toSimpleGraph := by
  classical
  refine ⟨deletedComponent_nonempty G C,
    no_isPerfectMatching_component_of_largest_max_defect G hMax hLargest C, ?_⟩
  intro c
  by_contra hNoExists
  have hNo : ∀ M : (deleteVertex C.toSimpleGraph c).Subgraph, ¬ M.IsPerfectMatching := by
    intro M hM
    exact hNoExists ⟨M, hM⟩
  obtain ⟨A, hA⟩ :=
    exists_local_tutte_surplus_of_no_deleteVertex_matching G hMax hLargest C c hNo
  have hCodd : C ∈ (delete_vertices G S).oddComponents :=
    all_components_odd_of_largest_max_defect G hMax hLargest C
  let T : Set V := localLiftSet C c A
  have hdef_le : defect G S ≤ defect G T := by
    simpa [T] using defect_le_localLiftSet_of_local_surplus G C hCodd c A hA
  have hdef_ge : defect G T ≤ defect G S := hMax T
  have hdef_eq : defect G T = defect G S := le_antisymm hdef_ge hdef_le
  have hcard_le : T.ncard ≤ S.ncard := hLargest T hdef_eq
  have hcard : T.ncard = S.ncard + 1 + A.ncard := by
    simpa [T] using ncard_deleted_union_singleton_union_localImage C c A
  omega

lemma defect_eq_tutteDefect (G : SimpleGraph V) [Finite V] (S : Set V) :
    defect G S =
      (((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard : ℤ) - S.ncard := by
  rw [defect, ← oddComponents_ncard_deleteVertsTop_eq_delete_vertices G S]

lemma isTutteViolator_iff_defect_pos (G : SimpleGraph V) [Finite V] (S : Set V) :
    G.IsTutteViolator S ↔ 0 < defect G S := by
  rw [SimpleGraph.IsTutteViolator, defect_eq_tutteDefect]
  omega

/--
If `T ⊆ S`, then every vertex surviving deletion of `S` also survives deletion
of `T`; hence `G - S` maps canonically into `G - T`.
-/
def deleteVerticesHomOfSubset (G : SimpleGraph V) {T S : Set V} (hTS : T ⊆ S) :
    delete_vertices G S →g delete_vertices G T where
  toFun x := ⟨x.1, fun hxT => x.2 (hTS hxT)⟩
  map_rel' := by
    intro x y hxy
    simpa [delete_vertices] using hxy

lemma walk_endpoint_in_component_of_no_adj_reintroduced
    {G : SimpleGraph V} [Finite V] {T S : Set V} (hTS : T ⊆ S)
    (C : DeletedComponent G S)
    (hNoAdj : ∀ x : (Sᶜ : Set V), x ∈ C.supp →
      ∀ y : V, y ∈ S → y ∉ T → ¬ G.Adj x.1 y)
    {x y : (Tᶜ : Set V)}
    (hxS : x.1 ∉ S) (hxC : (⟨x.1, hxS⟩ : (Sᶜ : Set V)) ∈ C.supp)
    (p : (delete_vertices G T).Walk x y) :
    ∃ hyS : y.1 ∉ S, (⟨y.1, hyS⟩ : (Sᶜ : Set V)) ∈ C.supp := by
  induction p with
  | nil =>
      exact ⟨hxS, hxC⟩
  | cons hxy p ih =>
      rename_i u z w
      have hG : G.Adj u.1 z.1 := by
        simpa [delete_vertices, SimpleGraph.induce] using hxy
      have hzT : z.1 ∉ T := z.2
      have hzS : z.1 ∉ S := by
        intro hzS
        exact hNoAdj ⟨u.1, hxS⟩ hxC z.1 hzS hzT hG
      have hHs : (delete_vertices G S).Adj
          (⟨u.1, hxS⟩ : (Sᶜ : Set V)) (⟨z.1, hzS⟩ : (Sᶜ : Set V)) := by
        simpa [delete_vertices, SimpleGraph.induce] using hG
      exact ih hzS (C.mem_supp_of_adj_mem_supp hxC hHs)

noncomputable def componentMapOfSubset
    (G : SimpleGraph V) [Finite V] {T S : Set V} (hTS : T ⊆ S)
    (C : DeletedComponent G S) : DeletedComponent G T :=
  let r := C.nonempty_supp.some
  (delete_vertices G T).connectedComponentMk
    ⟨r.1, fun hrT => r.2 (hTS hrT)⟩

noncomputable def componentSurvivalSuppEquiv
    (G : SimpleGraph V) [Finite V] {T S : Set V} (hTS : T ⊆ S)
    (C : DeletedComponent G S)
    (hNoAdj : ∀ x : (Sᶜ : Set V), x ∈ C.supp →
      ∀ y : V, y ∈ S → y ∉ T → ¬ G.Adj x.1 y) :
    C.supp ≃ (componentMapOfSubset G hTS C).supp where
  toFun x := by
    let xT : (Tᶜ : Set V) := ⟨x.1.1, fun hxT => x.1.2 (hTS hxT)⟩
    refine ⟨xT, ?_⟩
    let r := C.nonempty_supp.some
    let rT : (Tᶜ : Set V) := ⟨r.1, fun hrT => r.2 (hTS hrT)⟩
    have hxC : x.1 ∈ C.supp := x.2
    have hrC : r ∈ C.supp := C.nonempty_supp.some_mem
    have hcc : (delete_vertices G S).connectedComponentMk x.1 =
        (delete_vertices G S).connectedComponentMk r := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxC hrC
      rw [hxC, hrC]
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hcc
    have pT : (delete_vertices G T).Walk xT rT :=
      p.map (deleteVerticesHomOfSubset G hTS)
    have hccT :
        (delete_vertices G T).connectedComponentMk xT =
          (delete_vertices G T).connectedComponentMk rT :=
      SimpleGraph.ConnectedComponent.sound pT.reachable
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (componentMapOfSubset G hTS C) xT).2 (by
        simpa [componentMapOfSubset, r, rT] using hccT)
  invFun y := by
    let r := C.nonempty_supp.some
    let rT : (Tᶜ : Set V) := ⟨r.1, fun hrT => r.2 (hTS hrT)⟩
    have hrC : r ∈ C.supp := C.nonempty_supp.some_mem
    have hycc : (delete_vertices G T).connectedComponentMk y.1 =
        componentMapOfSubset G hTS C := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff
        (componentMapOfSubset G hTS C) y.1).1 y.2
    have hcc : (delete_vertices G T).connectedComponentMk rT =
        (delete_vertices G T).connectedComponentMk y.1 := by
      simpa [componentMapOfSubset, r, rT] using hycc.symm
    let p := Classical.choice (SimpleGraph.ConnectedComponent.exact hcc)
    let hres :=
      walk_endpoint_in_component_of_no_adj_reintroduced hTS C hNoAdj
        (x := rT) (y := y.1) r.2 hrC p
    let hyS := Classical.choose hres
    exact ⟨⟨y.1.1, hyS⟩, Classical.choose_spec hres⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

lemma odd_componentMapOfSubset_of_no_adj
    {G : SimpleGraph V} [Finite V] {T S : Set V} (hTS : T ⊆ S)
    (C : DeletedComponent G S)
    (hNoAdj : ∀ x : (Sᶜ : Set V), x ∈ C.supp →
      ∀ y : V, y ∈ S → y ∉ T → ¬ G.Adj x.1 y)
    (hOdd : Odd C.supp.ncard) :
    Odd (componentMapOfSubset G hTS C).supp.ncard := by
  have hcard : C.supp.ncard = (componentMapOfSubset G hTS C).supp.ncard := by
    simpa [Nat.card_coe_set_eq] using
      Nat.card_congr (componentSurvivalSuppEquiv G hTS C hNoAdj)
  rwa [← hcard]

lemma componentMapOfSubset_eq_imp_eq_of_no_adj
    {G : SimpleGraph V} [Finite V] {T S : Set V} (hTS : T ⊆ S)
    {C D : DeletedComponent G S}
    (hNoAdjD : ∀ x : (Sᶜ : Set V), x ∈ D.supp →
      ∀ y : V, y ∈ S → y ∉ T → ¬ G.Adj x.1 y)
    (hEq : componentMapOfSubset G hTS C = componentMapOfSubset G hTS D) :
    C = D := by
  let rC := C.nonempty_supp.some
  let rCT : (Tᶜ : Set V) := ⟨rC.1, fun hrT => rC.2 (hTS hrT)⟩
  have hrC : rC ∈ C.supp := C.nonempty_supp.some_mem
  have hrCmap : rCT ∈ (componentMapOfSubset G hTS C).supp := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (componentMapOfSubset G hTS C) rCT).2 (by
        simp [componentMapOfSubset, rC, rCT])
  have hrDmap : rCT ∈ (componentMapOfSubset G hTS D).supp := by
    simpa [hEq] using hrCmap
  let yD : (componentMapOfSubset G hTS D).supp := ⟨rCT, hrDmap⟩
  let eD := componentSurvivalSuppEquiv G hTS D hNoAdjD
  have hrD : (⟨rC.1, rC.2⟩ : (Sᶜ : Set V)) ∈ D.supp := by
    have hsub : (eD.symm yD).1 = (⟨rC.1, rC.2⟩ : (Sᶜ : Set V)) := by
      apply Subtype.ext
      rfl
    simpa [hsub] using (eD.symm yD).2
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hrC hrD

def NoAdjToReintroduced
    (G : SimpleGraph V) [Finite V] {T S : Set V}
    (C : DeletedComponent G S) : Prop :=
  ∀ x : (Sᶜ : Set V), x ∈ C.supp →
    ∀ y : V, y ∈ S → y ∉ T → ¬ G.Adj x.1 y

lemma closedOddComponents_ncard_le_after_delete
    (G : SimpleGraph V) [Finite V] {T S : Set V} (hTS : T ⊆ S) :
    {C : DeletedComponent G S | C ∈ (delete_vertices G S).oddComponents ∧
      NoAdjToReintroduced (T := T) (S := S) G C}.ncard ≤
        (delete_vertices G T).oddComponents.ncard := by
  classical
  let source : Set (DeletedComponent G S) :=
    {C | C ∈ (delete_vertices G S).oddComponents ∧
      NoAdjToReintroduced (T := T) (S := S) G C}
  let f : source → (delete_vertices G T).oddComponents := fun C =>
    ⟨componentMapOfSubset G hTS C.1,
      odd_componentMapOfSubset_of_no_adj hTS C.1 C.2.2 C.2.1⟩
  have hf : Function.Injective f := by
    intro C D hCD
    apply Subtype.ext
    apply componentMapOfSubset_eq_imp_eq_of_no_adj (G := G) hTS D.2.2
    exact congrArg Subtype.val hCD
  simpa [source, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

lemma noAdjToReintroduced_of_not_mem_componentNeighbors
    (G : SimpleGraph V) [Finite V] {S : Set V} (A : Set S)
    {C : DeletedComponent G S} (hCnot : C ∉ componentNeighbors G A) :
    NoAdjToReintroduced (T := S \ subtypeImageSet A) (S := S) G C := by
  intro x hxC y hyS hyT hxy
  have hyA : y ∈ subtypeImageSet A := by
    by_contra hyA
    exact hyT ⟨hyS, hyA⟩
  rcases hyA with ⟨a, haA, rfl⟩
  exact hCnot ⟨a, haA, ⟨⟨x, hxC⟩, hxy.symm⟩⟩

lemma oddComponents_diff_componentNeighbors_ncard_le_after_unremove
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hAllOdd : ∀ C : DeletedComponent G S, C ∈ (delete_vertices G S).oddComponents)
    (A : Set S) :
    (delete_vertices G S).oddComponents.ncard - (componentNeighbors G A).ncard ≤
      (delete_vertices G (S \ subtypeImageSet A)).oddComponents.ncard := by
  classical
  let T : Set V := S \ subtypeImageSet A
  have hTS : T ⊆ S := by
    intro x hx
    exact hx.1
  let oddSet : Set (DeletedComponent G S) := (delete_vertices G S).oddComponents
  let neigh : Set (DeletedComponent G S) := componentNeighbors G A
  let closedOdd : Set (DeletedComponent G S) :=
    {C | C ∈ oddSet ∧ NoAdjToReintroduced (T := T) (S := S) G C}
  have hneigh_subset : neigh ⊆ oddSet := by
    intro C _hC
    exact hAllOdd C
  have hdiff_subset_closed : oddSet \ neigh ⊆ closedOdd := by
    intro C hC
    exact ⟨hC.1, noAdjToReintroduced_of_not_mem_componentNeighbors G A hC.2⟩
  have hdiff_le_closed : (oddSet \ neigh).ncard ≤ closedOdd.ncard :=
    Set.ncard_le_ncard hdiff_subset_closed
  have hclosed_le :
      closedOdd.ncard ≤ (delete_vertices G T).oddComponents.ncard := by
    simpa [closedOdd, oddSet, T] using closedOddComponents_ncard_le_after_delete G hTS
  have hdiff_card : (oddSet \ neigh).ncard =
      (delete_vertices G S).oddComponents.ncard - (componentNeighbors G A).ncard := by
    rw [Set.ncard_diff hneigh_subset]
  rw [← hdiff_card]
  exact le_trans hdiff_le_closed hclosed_le

lemma defect_lt_of_componentNeighbors_lt
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hAllOdd : ∀ C : DeletedComponent G S, C ∈ (delete_vertices G S).oddComponents)
    {A : Set S} (hLt : (componentNeighbors G A).ncard < A.ncard) :
    defect G S < defect G (S \ subtypeImageSet A) := by
  classical
  have hLower :=
    oddComponents_diff_componentNeighbors_ncard_le_after_unremove
      (G := G) hAllOdd A
  have hTcard : (S \ subtypeImageSet A).ncard = S.ncard - A.ncard :=
    ncard_diff_subtypeImageSet (A := A)
  have hA_le_S : A.ncard ≤ S.ncard := by
    rw [← ncard_subtypeImageSet (A := A)]
    exact Set.ncard_le_ncard (subtypeImageSet_subset A)
  dsimp [defect]
  rw [hTcard]
  omega

lemma false_of_max_defect_and_not_matchable
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hAllOdd : ∀ C : DeletedComponent G S, C ∈ (delete_vertices G S).oddComponents)
    (hNoMatch : ¬ MatchableToDeletedComponents G S) :
    False := by
  classical
  obtain ⟨A, hA⟩ := exists_componentNeighbors_lt_of_not_matchable G S hNoMatch
  have hdef : defect G S < defect G (S \ subtypeImageSet A) :=
    defect_lt_of_componentNeighbors_lt G hAllOdd hA
  exact (not_lt_of_ge (hMax (S \ subtypeImageSet A))) hdef

lemma matchable_of_max_defect_and_all_components_odd
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hAllOdd : ∀ C : DeletedComponent G S, C ∈ (delete_vertices G S).oddComponents) :
    MatchableToDeletedComponents G S := by
  by_contra hNo
  exact false_of_max_defect_and_not_matchable G hMax hAllOdd hNo

lemma matchable_of_largest_max_defect
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hLargest : ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard) :
    MatchableToDeletedComponents G S :=
  matchable_of_max_defect_and_all_components_odd G hMax
    (all_components_odd_of_largest_max_defect G hMax hLargest)

lemma gallaiEdmondsSet_of_largest_max_defect
    (G : SimpleGraph V) [Finite V] {S : Set V}
    (hMax : ∀ T : Set V, defect G T ≤ defect G S)
    (hLargest : ∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard) :
    GallaiEdmondsSet G S :=
  ⟨matchable_of_largest_max_defect G hMax hLargest,
    factorCritical_component_of_largest_max_defect G hMax hLargest⟩

lemma exists_gallaiEdmondsSet (G : SimpleGraph V) [Finite V] :
    ∃ S : Set V, GallaiEdmondsSet G S := by
  obtain ⟨S, hMax, hLargest⟩ := exists_largest_max_defect_set G
  exact ⟨S, gallaiEdmondsSet_of_largest_max_defect G hMax hLargest⟩

lemma exists_largest_max_defect_set_odd_and_matchable
    (G : SimpleGraph V) [Finite V] :
    ∃ S : Set V,
      (∀ T : Set V, defect G T ≤ defect G S) ∧
        (∀ T : Set V, defect G T = defect G S → T.ncard ≤ S.ncard) ∧
          (∀ C : DeletedComponent G S, C ∈ (delete_vertices G S).oddComponents) ∧
            MatchableToDeletedComponents G S := by
  obtain ⟨S, hMax, hLargest⟩ := exists_largest_max_defect_set G
  exact ⟨S, hMax, hLargest,
    all_components_odd_of_largest_max_defect G hMax hLargest,
    matchable_of_largest_max_defect G hMax hLargest⟩

end GallaiEdmondsExistence

end Chapter02
end Diestel
