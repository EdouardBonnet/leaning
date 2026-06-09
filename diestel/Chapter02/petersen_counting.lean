import Chapter02.definitions_ch2
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter02

universe u

namespace PetersenCounting

variable {V : Type u} (G : SimpleGraph V)

/-- Edges of `G` incident with at least one vertex of `S`. -/
abbrev EdgesIncidentToSet (S : Set V) : Type u :=
  {e : G.edgeSet // ∃ v : V, v ∈ S ∧ v ∈ (e : Sym2 V)}

/-- Odd connected components of `G - S`, as they occur in Tutte's condition. -/
abbrev DeletedOddComponents [Finite V] (S : Set V) : Type u :=
  ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents

/-- The vertices of a deleted component, transported back to the original vertex type. -/
def deletedComponentVerts [Finite V] (S : Set V) (C : DeletedOddComponents G S) : Set V :=
  Subtype.val '' C.1.supp

/-- Edges joining a deleted component to the deleted set `S`. -/
abbrev BoundaryEdges [Finite V] (S : Set V) (C : DeletedOddComponents G S) : Type u :=
  {e : G.edgeSet //
    ∃ x : V, x ∈ deletedComponentVerts G S C ∧
      ∃ y : V, y ∈ S ∧ (e : Sym2 V) = s(x, y)}

/-- Darts whose tail lies in a deleted component. -/
abbrev ComponentDarts [Finite V] (S : Set V) (C : DeletedOddComponents G S) : Type u :=
  {d : G.Dart // d.fst ∈ deletedComponentVerts G S C}

/-- Darts whose two ends both lie in a deleted component. -/
abbrev InternalDarts [Finite V] (S : Set V) (C : DeletedOddComponents G S) : Type u :=
  {d : ComponentDarts G S C // d.1.snd ∈ deletedComponentVerts G S C}

/-- Darts leaving a deleted component. -/
abbrev BoundaryDarts [Finite V] (S : Set V) (C : DeletedOddComponents G S) : Type u :=
  {d : ComponentDarts G S C // d.1.snd ∉ deletedComponentVerts G S C}

lemma deletedComponentVerts_subset_compl [Finite V] (S : Set V)
    (C : DeletedOddComponents G S) :
    deletedComponentVerts G S C ⊆ Sᶜ := by
  rintro x ⟨x', _hx', rfl⟩
  exact x'.2.2

lemma mem_deletedComponentVerts_of_adj_of_not_mem
    [Finite V] (S : Set V) (C : DeletedOddComponents G S)
    {x y : V} (hx : x ∈ deletedComponentVerts G S C)
    (hxy : G.Adj x y) (hyS : y ∉ S) :
    y ∈ deletedComponentVerts G S C := by
  rcases hx with ⟨x', hx', rfl⟩
  let y' : ((⊤ : G.Subgraph).deleteVerts S).verts := ⟨y, by simp [hyS]⟩
  refine ⟨y', ?_, rfl⟩
  have hAdj :
      ((⊤ : G.Subgraph).deleteVerts S).coe.Adj x' y' := by
    exact (show ((⊤ : G.Subgraph).deleteVerts S).Adj x' y' from by
      rw [SimpleGraph.Subgraph.deleteVerts_adj]
      exact ⟨by trivial, x'.2.2, by trivial, hyS, hxy⟩)
  exact (C.1.mem_supp_congr_adj hAdj).mp hx'

lemma boundaryDart_snd_mem_deletedSet
    [Finite V] (S : Set V) (C : DeletedOddComponents G S)
    (d : BoundaryDarts G S C) :
    d.1.1.snd ∈ S := by
  by_contra hnotS
  exact d.2 (mem_deletedComponentVerts_of_adj_of_not_mem G S C d.1.2 d.1.1.adj hnotS)

/-- A boundary dart determines its underlying boundary edge. -/
def boundaryDartsToBoundaryEdges
    [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    BoundaryDarts G S C → BoundaryEdges G S C :=
  fun d =>
    ⟨⟨d.1.1.edge, d.1.1.edge_mem⟩,
      ⟨d.1.1.fst, d.1.2, d.1.1.snd, boundaryDart_snd_mem_deletedSet G S C d, rfl⟩⟩

/-- A boundary edge has a unique orientation leaving the deleted component. -/
noncomputable def boundaryEdgesToBoundaryDarts
    [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    BoundaryEdges G S C → BoundaryDarts G S C :=
  fun e =>
    let x := e.2.choose
    let hxC := e.2.choose_spec.1
    let y := e.2.choose_spec.2.choose
    let hyS := e.2.choose_spec.2.choose_spec.1
    let hxy := e.2.choose_spec.2.choose_spec.2
    have hAdj : G.Adj x y := by
      rw [← SimpleGraph.mem_edgeSet, ← hxy]
      exact e.1.2
    ⟨⟨⟨(x, y), hAdj⟩, hxC⟩,
      fun hyC => (deletedComponentVerts_subset_compl G S C hyC) hyS⟩

noncomputable def boundaryDartsEquivBoundaryEdges
    [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    BoundaryDarts G S C ≃ BoundaryEdges G S C where
  toFun := boundaryDartsToBoundaryEdges G S C
  invFun := boundaryEdgesToBoundaryDarts G S C
  left_inv := by
    intro d
    apply Subtype.ext
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    let e : BoundaryEdges G S C := boundaryDartsToBoundaryEdges G S C d
    let x := e.2.choose
    let hxC := e.2.choose_spec.1
    let y := e.2.choose_spec.2.choose
    let hyS := e.2.choose_spec.2.choose_spec.1
    let hxy := e.2.choose_spec.2.choose_spec.2
    have hEdge : d.1.1.edge = s(x, y) := by
      simpa [e, boundaryDartsToBoundaryEdges] using hxy
    have hcases := (SimpleGraph.dart_edge_eq_mk'_iff'.mp hEdge)
    rcases hcases with hcases | hcases
    · exact Prod.ext hcases.1.symm hcases.2.symm
    · exfalso
      have hyC : y ∈ deletedComponentVerts G S C := hcases.1 ▸ d.1.2
      exact (deletedComponentVerts_subset_compl G S C hyC) hyS
  right_inv := by
    intro e
    apply Subtype.ext
    apply Subtype.ext
    let x := e.2.choose
    let y := e.2.choose_spec.2.choose
    let hxy := e.2.choose_spec.2.choose_spec.2
    exact hxy.symm

/-- Darts based in a component are the same as choosing the base vertex and a neighbour. -/
def componentDartsEquivSigma
    [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    ComponentDarts G S C ≃
      Sigma fun v : deletedComponentVerts G S C => G.neighborSet v.1 where
  toFun d := ⟨⟨d.1.fst, d.2⟩, ⟨d.1.snd, d.1.adj⟩⟩
  invFun p := ⟨⟨(p.1.1, p.2.1), p.2.2⟩, p.1.2⟩
  left_inv d := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    rfl
  right_inv p := by
    cases p with
    | mk v w =>
      cases v
      cases w
      rfl

lemma natCard_deletedComponentVerts_eq
    [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    Nat.card (deletedComponentVerts G S C) = C.1.supp.ncard := by
  classical
  rw [deletedComponentVerts, Nat.card_coe_set_eq]
  exact Set.ncard_image_of_injective C.1.supp Subtype.val_injective

lemma natCard_componentDarts_eq_three_mul
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (C : DeletedOddComponents G S) :
    Nat.card (ComponentDarts G S C) =
      3 * Nat.card (deletedComponentVerts G S C) := by
  classical
  calc
    Nat.card (ComponentDarts G S C) =
        Nat.card (Sigma fun v : deletedComponentVerts G S C => G.neighborSet v.1) :=
      Nat.card_congr (componentDartsEquivSigma G S C)
    _ = ∑ v : deletedComponentVerts G S C, Nat.card (G.neighborSet v.1) :=
      Nat.card_sigma
    _ = ∑ v : deletedComponentVerts G S C, G.degree v.1 := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Nat.card_eq_fintype_card]
      exact G.card_neighborSet_eq_degree v.1
    _ = ∑ _v : deletedComponentVerts G S C, 3 := by
      exact Finset.sum_congr rfl fun v _hv => hG.degree_eq v.1
    _ = 3 * Nat.card (deletedComponentVerts G S C) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, mul_comm]
      simp

lemma odd_natCard_componentDarts_of_cubic
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (C : DeletedOddComponents G S) :
    Odd (Nat.card (ComponentDarts G S C)) := by
  classical
  rw [natCard_componentDarts_eq_three_mul G S hG C]
  have hVerts : Odd (Nat.card (deletedComponentVerts G S C)) := by
    rw [natCard_deletedComponentVerts_eq G S C]
    exact C.2
  exact (show Odd 3 from by norm_num).mul hVerts

noncomputable def internalDartSymm
    [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    Equiv.Perm (InternalDarts G S C) where
  toFun d := ⟨⟨d.1.1.symm, d.2⟩, d.1.2⟩
  invFun d := ⟨⟨d.1.1.symm, d.2⟩, d.1.2⟩
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    exact SimpleGraph.Dart.symm_symm d.1.1
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    exact SimpleGraph.Dart.symm_symm d.1.1

lemma internalDartSymm_apply_ne
    [Finite V] (S : Set V) (C : DeletedOddComponents G S)
    (d : InternalDarts G S C) :
    internalDartSymm G S C d ≠ d := by
  intro h
  have hdart : d.1.1.symm = d.1.1 :=
    congrArg (fun z : InternalDarts G S C => z.1.1) h
  exact d.1.1.symm_ne hdart

lemma even_natCard_internalDarts
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (C : DeletedOddComponents G S) :
    Even (Nat.card (InternalDarts G S C)) := by
  classical
  let σ := internalDartSymm G S C
  have hsq : σ ^ 2 = 1 := by
    apply Equiv.ext
    intro d
    change σ (σ d) = d
    apply Subtype.ext
    apply Subtype.ext
    exact SimpleGraph.Dart.symm_symm d.1.1
  have hdiv : 2 ∣ σ.support.card := Equiv.Perm.two_dvd_card_support hsq
  have hsupport : σ.support = Finset.univ := by
    ext d
    rw [Equiv.Perm.mem_support]
    simpa [σ] using
      (iff_true_intro (internalDartSymm_apply_ne G S C d) :
        internalDartSymm G S C d ≠ d ↔ True)
  have hdivCard : 2 ∣ Fintype.card (InternalDarts G S C) := by
    rwa [hsupport, Finset.card_univ] at hdiv
  rw [Nat.card_eq_fintype_card]
  exact even_iff_two_dvd.mpr hdivCard

lemma natCard_boundaryDarts_eq_component_sub_internal
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (C : DeletedOddComponents G S) :
    Nat.card (BoundaryDarts G S C) =
      Nat.card (ComponentDarts G S C) - Nat.card (InternalDarts G S C) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_compl
    (fun d : ComponentDarts G S C => d.1.snd ∈ deletedComponentVerts G S C)

lemma odd_natCard_boundaryDarts_of_cubic
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (C : DeletedOddComponents G S) :
    Odd (Nat.card (BoundaryDarts G S C)) := by
  classical
  rw [natCard_boundaryDarts_eq_component_sub_internal G S C]
  have hle :
      Nat.card (InternalDarts G S C) ≤ Nat.card (ComponentDarts G S C) :=
    Finite.card_subtype_le
      (fun d : ComponentDarts G S C => d.1.snd ∈ deletedComponentVerts G S C)
  exact Nat.Odd.sub_even hle
    (odd_natCard_componentDarts_of_cubic G S hG C)
    (even_natCard_internalDarts G S C)

lemma boundary_natCard_odd_of_cubic
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (C : DeletedOddComponents G S) :
    Odd (Nat.card (BoundaryEdges G S C)) := by
  classical
  rw [Nat.card_congr (boundaryDartsEquivBoundaryEdges G S C).symm]
  exact odd_natCard_boundaryDarts_of_cubic G S hG C

lemma boundaryEdge_edgesIncidentToSet_spec [Finite V] (S : Set V)
    (C : DeletedOddComponents G S) (e : BoundaryEdges G S C) :
    ∃ v : V, v ∈ S ∧ v ∈ (e.1 : Sym2 V) := by
  rcases e.2 with ⟨x, _hx, y, hyS, hxy⟩
  exact ⟨y, hyS, by rw [hxy]; exact Sym2.mem_mk_right x y⟩

/-- Boundary edges are, in particular, edges incident with `S`. -/
def boundaryEdgesToIncident [Finite V] (S : Set V) (C : DeletedOddComponents G S) :
    BoundaryEdges G S C ↪ EdgesIncidentToSet G S where
  toFun e := ⟨e.1, boundaryEdge_edgesIncidentToSet_spec G S C e⟩
  inj' e f hef := by
    apply Subtype.ext
    exact congrArg (fun z : EdgesIncidentToSet G S => (z.1 : G.edgeSet)) hef

lemma deletedOddComponent_eq_of_common_vertex [Finite V] (S : Set V)
    {C D : DeletedOddComponents G S} {x : V}
    (hxC : x ∈ deletedComponentVerts G S C)
    (hxD : x ∈ deletedComponentVerts G S D) :
    C = D := by
  rcases hxC with ⟨xC, hxC, rfl⟩
  rcases hxD with ⟨xD, hxD, hxD_eq⟩
  have hvertex : xD = xC := Subtype.ext hxD_eq
  apply Subtype.ext
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hxC (hvertex ▸ hxD)

lemma boundaryEdges_component_eq_of_edge_eq [Finite V] (S : Set V)
    {C D : DeletedOddComponents G S} (eC : BoundaryEdges G S C)
    (eD : BoundaryEdges G S D) (hedge : (eC.1 : G.edgeSet) = eD.1) :
    C = D := by
  rcases eC.2 with ⟨x, hxC, y, hyS, hxy⟩
  rcases eD.2 with ⟨x', hxD, y', hy'S, hx'y'⟩
  have hx_notS : x ∉ S := deletedComponentVerts_subset_compl G S C hxC
  have hx'_notS : x' ∉ S := deletedComponentVerts_subset_compl G S D hxD
  have hsym : s(x, y) = s(x', y') := by
    calc
      s(x, y) = (eC.1 : Sym2 V) := hxy.symm
      _ = (eD.1 : Sym2 V) := congrArg (fun e : G.edgeSet => (e : Sym2 V)) hedge
      _ = s(x', y') := hx'y'
  simp only [Sym2.eq, Sym2.rel_iff] at hsym
  rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact deletedOddComponent_eq_of_common_vertex G S hxC hxD
  · exact (hx_notS hy'S).elim

lemma boundaryEdge_isBridge_of_unique
    [Finite V] (S : Set V) (C : DeletedOddComponents G S)
    (e : BoundaryEdges G S C)
    (huniq : ∀ f : BoundaryEdges G S C, (f.1 : G.edgeSet) = e.1) :
    G.IsBridge (e.1 : Sym2 V) := by
  classical
  rcases e.2 with ⟨x, hxC, y, hyS, hxy⟩
  rw [hxy]
  rw [SimpleGraph.isBridge_iff]
  refine ⟨?_, ?_⟩
  · simpa [hxy] using e.1.2
  · intro hreach
    have hyC : y ∈ deletedComponentVerts G S C := by
      let H : (G.deleteEdges {s(x, y)}).Subgraph :=
        (⊤ : (G.deleteEdges {s(x, y)}).Subgraph).induce (deletedComponentVerts G S C)
      have hclosed :
          ∀ v ∈ H.verts, ∀ w : V, (G.deleteEdges {s(x, y)}).Adj v w → H.Adj v w := by
        intro v hv w hvw
        have hvC : v ∈ deletedComponentVerts G S C := by
          simpa [H] using hv
        have hGvw : G.Adj v w := (SimpleGraph.deleteEdges_adj.mp hvw).1
        have hnotEdge : s(v, w) ∉ ({s(x, y)} : Set (Sym2 V)) :=
          (SimpleGraph.deleteEdges_adj.mp hvw).2
        by_cases hwS : w ∈ S
        · let f : BoundaryEdges G S C :=
            ⟨⟨s(v, w), by simpa [SimpleGraph.mem_edgeSet] using hGvw⟩,
              ⟨v, hvC, w, hwS, rfl⟩⟩
          have hf : (f.1 : G.edgeSet) = e.1 := huniq f
          have hsym : s(v, w) = s(x, y) := by
            calc
              s(v, w) = (f.1 : Sym2 V) := rfl
              _ = (e.1 : Sym2 V) := congrArg (fun a : G.edgeSet => (a : Sym2 V)) hf
              _ = s(x, y) := hxy
          exact (hnotEdge (by simpa [hsym])).elim
        · have hwC : w ∈ deletedComponentVerts G S C :=
            mem_deletedComponentVerts_of_adj_of_not_mem G S C hvC hGvw hwS
          simpa [H, hvC, hwC] using hvw
      exact hreach.mem_subgraphVerts (H := H) hclosed hxC
    exact (deletedComponentVerts_subset_compl G S C hyC) hyS

lemma boundary_natCard_ne_one_of_bridgeless
    [Finite V] (S : Set V) (hBridgeless : IsBridgeless G)
    (C : DeletedOddComponents G S) :
    Nat.card (BoundaryEdges G S C) ≠ 1 := by
  intro hcard
  obtain ⟨e, huniq⟩ := (Nat.card_eq_one_iff_exists).mp hcard
  have hBridge : G.IsBridge (e.1 : Sym2 V) :=
    boundaryEdge_isBridge_of_unique G S C e fun f =>
      congrArg (fun a : BoundaryEdges G S C => (a.1 : G.edgeSet)) (huniq f)
  exact hBridgeless (e.1 : Sym2 V) e.1.2 hBridge

/--
Local embeddings of `Fin 3` into every component boundary glue to one global
embedding into the set of edges incident with `S`.
-/
def oddComponentTripleEmbeddingOfBoundaryEmbeddings [Finite V] (S : Set V)
    (ψ : ∀ C : DeletedOddComponents G S, Fin 3 ↪ BoundaryEdges G S C) :
    DeletedOddComponents G S × Fin 3 ↪ EdgesIncidentToSet G S where
  toFun ci := boundaryEdgesToIncident G S ci.1 (ψ ci.1 ci.2)
  inj' a b hab := by
    rcases a with ⟨C, i⟩
    rcases b with ⟨D, j⟩
    have hedge : ((ψ C i).1 : G.edgeSet) = (ψ D j).1 :=
      congrArg (fun z : EdgesIncidentToSet G S => (z.1 : G.edgeSet)) hab
    have hCD : C = D := boundaryEdges_component_eq_of_edge_eq G S (ψ C i) (ψ D j) hedge
    subst D
    have hBoundary : ψ C i = ψ C j :=
      (boundaryEdgesToIncident G S C).injective hab
    exact Prod.ext rfl ((ψ C).injective hBoundary)

/-- The local incidence type used in Chapter 2 is equivalent to Mathlib's incidence set. -/
def incidentEdgeEquivIncidenceSet (v : V) : IncidentEdge G v ≃ G.incidenceSet v where
  toFun e := ⟨(e.1 : Sym2 V), by exact ⟨e.1.2, e.2⟩⟩
  invFun e := ⟨⟨e.1, e.2.1⟩, e.2.2⟩
  left_inv e := by
    cases e
    rfl
  right_inv e := by
    cases e
    rfl

lemma natCard_incidentEdge_eq_degree [Fintype V] [DecidableRel G.Adj] (v : V) :
    Nat.card (IncidentEdge G v) = G.degree v := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (incidentEdgeEquivIncidenceSet G v)).trans
    (G.card_incidenceSet_eq_degree (v := v))

/-- Choose one endpoint in `S` for each edge incident with `S`. -/
noncomputable def edgesIncidentToSetToSigma (S : Set V) :
    EdgesIncidentToSet G S → Sigma fun v : S => IncidentEdge G v :=
  fun e =>
    ⟨⟨e.2.choose, e.2.choose_spec.1⟩, ⟨e.1, e.2.choose_spec.2⟩⟩

lemma edgesIncidentToSetToSigma_injective (S : Set V) :
    Function.Injective (edgesIncidentToSetToSigma G S) := by
  intro e f hef
  apply Subtype.ext
  have hEdge :
      ((edgesIncidentToSetToSigma G S e).2.1 : G.edgeSet) =
        ((edgesIncidentToSetToSigma G S f).2.1 : G.edgeSet) :=
    congrArg (fun z : Sigma fun v : S => IncidentEdge G v => (z.2.1 : G.edgeSet)) hef
  simpa [edgesIncidentToSetToSigma] using hEdge

lemma natCard_edgesIncidentToSet_le_sum_degrees
    [Fintype V] [DecidableRel G.Adj] (S : Set V) [Fintype S] :
    Nat.card (EdgesIncidentToSet G S) ≤ ∑ v : S, G.degree v := by
  classical
  have hcard :
      Nat.card (EdgesIncidentToSet G S) ≤
        Nat.card (Sigma fun v : S => IncidentEdge G v) :=
    Nat.card_le_card_of_injective (edgesIncidentToSetToSigma G S)
      (edgesIncidentToSetToSigma_injective G S)
  calc
    Nat.card (EdgesIncidentToSet G S) ≤
        Nat.card (Sigma fun v : S => IncidentEdge G v) := hcard
    _ = ∑ v : S, G.degree v := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      exact Finset.sum_congr rfl fun v _ => by
        rw [← Nat.card_eq_fintype_card]
        exact natCard_incidentEdge_eq_degree G v

lemma natCard_edgesIncidentToSet_le_three_mul_ncard_of_cubic
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G) :
    Nat.card (EdgesIncidentToSet G S) ≤ 3 * S.ncard := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  calc
    Nat.card (EdgesIncidentToSet G S) ≤ ∑ v : S, G.degree v :=
      natCard_edgesIncidentToSet_le_sum_degrees G S
    _ = ∑ _v : S, 3 := by
      exact Finset.sum_congr rfl fun v _ => hG.degree_eq v
    _ = 3 * S.ncard := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_comm]
      congr 1
      simpa using (Nat.card_coe_set_eq S)

lemma natCard_deletedOddComponents_prod_fin_three
    [Fintype V] [DecidableRel G.Adj] (S : Set V) :
    Nat.card (DeletedOddComponents G S × Fin 3) =
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard * 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
  congr 1
  rw [← Nat.card_eq_fintype_card (α := DeletedOddComponents G S), Nat.card_coe_set_eq]

/--
Counting form of Petersen's argument: if every odd component of `G - S` can be
assigned three distinct edges incident with `S`, then a cubic graph has no Tutte
violator at `S`.
-/
lemma not_isTutteViolator_of_oddComponent_triple_embedding
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (φ : DeletedOddComponents G S × Fin 3 ↪ EdgesIncidentToSet G S) :
    ¬ G.IsTutteViolator S := by
  classical
  intro hTutte
  have hEmbedding :
      Nat.card (DeletedOddComponents G S × Fin 3) ≤ Nat.card (EdgesIncidentToSet G S) :=
    Nat.card_le_card_of_injective φ φ.injective
  have hIncident :
      Nat.card (EdgesIncidentToSet G S) ≤ 3 * S.ncard :=
    natCard_edgesIncidentToSet_le_three_mul_ncard_of_cubic G S hG
  have hMul :
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard * 3 ≤ S.ncard * 3 := by
    calc
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard * 3 =
          Nat.card (DeletedOddComponents G S × Fin 3) :=
        (natCard_deletedOddComponents_prod_fin_three G S).symm
      _ ≤ Nat.card (EdgesIncidentToSet G S) := hEmbedding
      _ ≤ 3 * S.ncard := hIncident
      _ = S.ncard * 3 := by rw [mul_comm]
  have hOddLeS :
      ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ S.ncard :=
    Nat.le_of_mul_le_mul_right hMul (by decide : 0 < 3)
  exact (not_le_of_gt hTutte) hOddLeS

lemma not_isTutteViolator_of_boundary_embeddings
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (ψ : ∀ C : DeletedOddComponents G S, Fin 3 ↪ BoundaryEdges G S C) :
    ¬ G.IsTutteViolator S :=
  not_isTutteViolator_of_oddComponent_triple_embedding G S hG
    (oddComponentTripleEmbeddingOfBoundaryEmbeddings G S ψ)

lemma nonempty_boundaryEmbedding_of_three_le_natCard
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (C : DeletedOddComponents G S)
    (hC : 3 ≤ Nat.card (BoundaryEdges G S C)) :
    Nonempty (Fin 3 ↪ BoundaryEdges G S C) := by
  classical
  apply Function.Embedding.nonempty_of_card_le
  simpa [Nat.card_eq_fintype_card] using hC

lemma not_isTutteViolator_of_boundary_natCard_ge_three
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (hBoundary : ∀ C : DeletedOddComponents G S, 3 ≤ Nat.card (BoundaryEdges G S C)) :
    ¬ G.IsTutteViolator S := by
  classical
  refine not_isTutteViolator_of_boundary_embeddings G S hG fun C => ?_
  exact Classical.choice (nonempty_boundaryEmbedding_of_three_le_natCard G S C (hBoundary C))

lemma three_le_of_odd_ne_one {n : ℕ} (hodd : Odd n) (hne : n ≠ 1) : 3 ≤ n := by
  rcases hodd with ⟨k, rfl⟩
  cases k with
  | zero => exact (hne rfl).elim
  | succ k => omega

lemma not_isTutteViolator_of_boundary_odd_and_ne_one
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (hG : IsCubic G)
    (hOdd : ∀ C : DeletedOddComponents G S, Odd (Nat.card (BoundaryEdges G S C)))
    (hNeOne : ∀ C : DeletedOddComponents G S, Nat.card (BoundaryEdges G S C) ≠ 1) :
    ¬ G.IsTutteViolator S :=
  not_isTutteViolator_of_boundary_natCard_ge_three G S hG fun C =>
    three_le_of_odd_ne_one (hOdd C) (hNeOne C)

end PetersenCounting

end Chapter02
end Diestel
