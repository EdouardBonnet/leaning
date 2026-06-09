import Chapter02.cycle_packing_induction_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma deleteVerts_loopless {G : MultiGraph V E} (hG : G.Loopless)
    (X : Set V) :
    Loopless (G.deleteVerts X) := by
  intro e he x hloop
  change (G.deleteVerts X).IsLink e x x at hloop
  rw [Graph.deleteVerts_isLink] at hloop
  exact hG hloop.1.edge_mem x hloop.1

lemma cycle_edgeSupport_subset_edgeSet {G : MultiGraph V E}
    (C : G.CycleIn) :
    C.edgeSupport ⊆ G.edgeSet := by
  intro e he
  exact (C.edges_inside he).1

lemma cycle_incident_edge_mem_vertexSet {G : MultiGraph V E}
    (C : G.CycleIn) {e : E} (he : e ∈ C.edgeSupport)
    {v : V} (hinc : G.Inc e v) :
    v ∈ C.support :=
  (C.edges_inside he).2 v hinc

lemma cycle_incident_edge_mem_support_iff {G : MultiGraph V E}
    (C : G.CycleIn) {e : E} (he : e ∈ C.edgeSupport)
    {v : V} :
    G.Inc e v → v ∈ C.support :=
  cycle_incident_edge_mem_vertexSet C he

private noncomputable def cycleIncidentSubtypeEquivSet {G : MultiGraph V E}
    (C : G.CycleIn) (v : V) :
    {e : C.edgeSupport // G.Inc e.1 v} ≃
      {e : E // e ∈ C.edgeSupport ∧ G.Inc e v} where
  toFun e := ⟨e.1.1, e.1.2, e.2⟩
  invFun e := ⟨⟨e.1, e.2.1⟩, e.2.2⟩
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro e
    rfl

lemma cycle_incident_edge_set_ncard {G : MultiGraph V E}
    (C : G.CycleIn) {v : V} (hv : v ∈ C.support) :
    ({e : E | e ∈ C.edgeSupport ∧ G.Inc e v} : Set E).ncard = 2 := by
  classical
  have hcard :
      Nat.card {e : E // e ∈ C.edgeSupport ∧ G.Inc e v} = 2 := by
    rw [← Nat.card_congr (cycleIncidentSubtypeEquivSet (G := G) C v)]
    exact C.degree_two v hv
  simpa using hcard

lemma incident_edge_set_ncard_of_cubic {G : MultiGraph V E} [Finite E]
    (hCubic : G.IsCubic) {v : V} (hv : v ∈ G.vertexSet) :
    ({e : E | G.Incident v e} : Set E).ncard = 3 := by
  change Nat.card {e : E // G.Incident v e} = 3
  exact hCubic.2 v hv

lemma cycle_incident_complement_ncard_eq_one {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsCubic) (C : G.CycleIn)
    {v : V} (hv : v ∈ C.support) :
    ({e : E | G.Incident v e ∧ e ∉ C.edgeSupport} : Set E).ncard = 1 := by
  classical
  let A : Set E := {e : E | G.Incident v e}
  let B : Set E := {e : E | e ∈ C.edgeSupport ∧ G.Inc e v}
  have hBA : B ⊆ A := by
    intro e he
    exact ⟨(C.edges_inside he.1).1, he.2⟩
  have hA : A.ncard = 3 := by
    exact incident_edge_set_ncard_of_cubic (G := G) hCubic (C.support_subset_vertexSet hv)
  have hB : B.ncard = 2 := by
    exact cycle_incident_edge_set_ncard (G := G) C hv
  have hdiff : (A \ B).ncard = 1 := by
    rw [Set.ncard_diff hBA]
    omega
  have hset :
      ({e : E | G.Incident v e ∧ e ∉ C.edgeSupport} : Set E) = A \ B := by
    ext e
    constructor
    · rintro ⟨heA, heC⟩
      exact ⟨heA, by
        intro heB
        exact heC heB.1⟩
    · rintro ⟨heA, heB⟩
      exact ⟨heA, by
        intro heC
        exact heB ⟨heC, heA.2⟩⟩
  rw [hset]
  exact hdiff

private noncomputable def edgeBoundaryInsideEndpoint {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) : U :=
  ⟨Classical.choose e.2.2,
    (Classical.choose_spec (Classical.choose_spec e.2.2)).2.1⟩

private lemma edgeBoundaryInsideEndpoint_isLink {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) :
    G.IsLink e.1 (edgeBoundaryInsideEndpoint (G := G) U e).1
      (Classical.choose (Classical.choose_spec e.2.2)) := by
  exact (Classical.choose_spec (Classical.choose_spec e.2.2)).1

private lemma edgeBoundaryInsideEndpoint_outside {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) :
    Classical.choose (Classical.choose_spec e.2.2) ∉ U := by
  exact (Classical.choose_spec (Classical.choose_spec e.2.2)).2.2.2

private lemma edgeBoundaryInsideEndpoint_inc {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) :
    G.Inc e.1 (edgeBoundaryInsideEndpoint (G := G) U e).1 :=
  (edgeBoundaryInsideEndpoint_isLink (G := G) U e).inc_left

private lemma edgeBoundary_not_mem_cycle_edgeSupport {G : MultiGraph V E}
    (C : G.CycleIn) (e : G.edgeBoundary C.support) :
    e.1 ∉ C.edgeSupport := by
  intro heC
  have hy :
      Classical.choose (Classical.choose_spec e.2.2) ∈ C.support :=
    (C.edges_inside heC).2 (Classical.choose (Classical.choose_spec e.2.2))
      (edgeBoundaryInsideEndpoint_isLink (G := G) C.support e).inc_right
  exact edgeBoundaryInsideEndpoint_outside (G := G) C.support e hy

private lemma edgeBoundary_edge_mem_incident_complement {G : MultiGraph V E}
    (C : G.CycleIn) (e : G.edgeBoundary C.support) :
    e.1 ∈
      ({f : E | G.Incident (edgeBoundaryInsideEndpoint (G := G) C.support e).1 f ∧
        f ∉ C.edgeSupport} : Set E) := by
  exact ⟨⟨e.2.1, edgeBoundaryInsideEndpoint_inc (G := G) C.support e⟩,
    edgeBoundary_not_mem_cycle_edgeSupport (G := G) C e⟩

lemma edgeBoundaryInsideEndpoint_injective {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsCubic) (C : G.CycleIn) :
    Function.Injective (edgeBoundaryInsideEndpoint (G := G) C.support) := by
  intro e f hef
  have hv : (edgeBoundaryInsideEndpoint (G := G) C.support e).1 ∈ C.support :=
    (edgeBoundaryInsideEndpoint (G := G) C.support e).2
  let S : Set E :=
    {g : E | G.Incident (edgeBoundaryInsideEndpoint (G := G) C.support e).1 g ∧
      g ∉ C.edgeSupport}
  have hS : S.ncard = 1 := by
    exact cycle_incident_complement_ncard_eq_one (G := G) hCubic C hv
  obtain ⟨a, hSsingleton⟩ := Set.ncard_eq_one.mp hS
  have heS : e.1 ∈ S :=
    edgeBoundary_edge_mem_incident_complement (G := G) C e
  have hfS : f.1 ∈ S := by
    have hfS' :
        f.1 ∈
          ({g : E | G.Incident (edgeBoundaryInsideEndpoint (G := G) C.support f).1 g ∧
            g ∉ C.edgeSupport} : Set E) :=
      edgeBoundary_edge_mem_incident_complement (G := G) C f
    simpa [S, hef] using hfS'
  rw [hSsingleton] at heS hfS
  simp only [Set.mem_singleton_iff] at heS hfS
  exact Subtype.ext (heS.trans hfS.symm)

lemma edgeBoundary_ncard_le_cycle_support_ncard {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsCubic) (C : G.CycleIn) :
    (G.edgeBoundary C.support).ncard ≤ C.support.ncard := by
  classical
  have hinj := edgeBoundaryInsideEndpoint_injective (G := G) hCubic C
  have hcard :=
    Nat.card_le_card_of_injective
      (edgeBoundaryInsideEndpoint (G := G) C.support) hinj
  simpa using hcard

lemma deleteVerts_incident_subset_original {G : MultiGraph V E}
    (U : Set V) (v : V) :
    ({e : E | Incident (G.deleteVerts U) v e} : Set E) ⊆
      ({e : E | G.Incident v e} : Set E) := by
  intro e he
  exact ⟨(Graph.deleteVerts_le (G := G) (X := U)).edgeSet_mono he.1,
    (inc_iff_of_subgraph_edge (Graph.deleteVerts_le (G := G) (X := U)) he.1).mp he.2⟩

lemma deleteVerts_incident_set_ncard_eq_degree {G : MultiGraph V E}
    [Finite E] (U : Set V) (v : V) :
    ({e : E | Incident (G.deleteVerts U) v e} : Set E).ncard =
      degree (G.deleteVerts U) v := by
  rfl

lemma original_incident_not_deleteVerts_ncard_ge_two {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsCubic) {U : Set V} {v : V}
    (hv : v ∈ G.vertexSet)
    (hdeg : degree (G.deleteVerts U) v ≤ 1) :
    2 ≤ ({e : E | G.Incident v e ∧ ¬ Incident (G.deleteVerts U) v e} : Set E).ncard := by
  classical
  let A : Set E := {e : E | G.Incident v e}
  let B : Set E := {e : E | Incident (G.deleteVerts U) v e}
  have hBA : B ⊆ A := deleteVerts_incident_subset_original (G := G) U v
  have hA : A.ncard = 3 := incident_edge_set_ncard_of_cubic (G := G) hCubic hv
  have hB : B.ncard ≤ 1 := by
    rw [deleteVerts_incident_set_ncard_eq_degree (G := G) U v]
    exact hdeg
  have hdiff : 2 ≤ (A \ B).ncard := by
    rw [Set.ncard_diff hBA]
    omega
  have hset :
      ({e : E | G.Incident v e ∧ ¬ Incident (G.deleteVerts U) v e} : Set E) = A \ B := by
    ext e
    rfl
  rw [hset]
  exact hdiff

lemma original_incident_not_deleteVerts_mem_edgeBoundary {G : MultiGraph V E}
    {U : Set V} {v : V} {e : E}
    (hinc : G.Incident v e) (hvU : v ∉ U)
    (hnot : ¬ Incident (G.deleteVerts U) v e) :
    e ∈ G.edgeBoundary U := by
  classical
  obtain ⟨w, hlink⟩ := hinc.2
  have hwU : w ∈ U := by
    by_contra hwU
    have hdelLink : (G.deleteVerts U).IsLink e v w := by
      rw [Graph.deleteVerts_isLink]
      exact ⟨hlink, hvU, hwU⟩
    exact hnot ⟨hdelLink.edge_mem, hdelLink.inc_left⟩
  exact ⟨hinc.1, w, v, hlink.symm, hwU, hlink.left_mem, hvU⟩

lemma edgeBoundary_incident_outside_not_deleteVerts {G : MultiGraph V E}
    {U : Set V} {v : V} {e : E}
    (heB : e ∈ G.edgeBoundary U) (hinc : G.Incident v e)
    (hvU : v ∉ U) :
    ¬ Incident (G.deleteVerts U) v e := by
  classical
  rintro hdel
  rcases heB with ⟨heG, x, y, hxy, hxU, hyG, hyU⟩
  obtain ⟨z, hvzDel⟩ := hdel.2
  rw [Graph.deleteVerts_isLink] at hvzDel
  rcases hxy.eq_and_eq_or_eq_and_eq hvzDel.1 with hsame | hswap
  · exact hvU (hsame.1 ▸ hxU)
  · exact hvzDel.2.2 (hswap.1 ▸ hxU)

lemma incident_boundary_set_eq_original_not_deleteVerts {G : MultiGraph V E}
    {U : Set V} {v : V} (hvU : v ∉ U) :
    ({e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e} : Set E) =
      {e : E | G.Incident v e ∧ ¬ Incident (G.deleteVerts U) v e} := by
  ext e
  constructor
  · rintro ⟨heB, hinc⟩
    exact ⟨hinc, edgeBoundary_incident_outside_not_deleteVerts
      (G := G) heB hinc hvU⟩
  · rintro ⟨hinc, hnot⟩
    exact ⟨original_incident_not_deleteVerts_mem_edgeBoundary
      (G := G) hinc hvU hnot, hinc⟩

lemma incident_boundary_ncard_ge_two_of_deleteVerts_degree_le_one
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : degree (G.deleteVerts U) v ≤ 1) :
    2 ≤ ({e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e} : Set E).ncard := by
  rw [incident_boundary_set_eq_original_not_deleteVerts (G := G) (U := U) (v := v) hvU]
  exact original_incident_not_deleteVerts_ncard_ge_two (G := G) hCubic hv hdeg

lemma edgeBoundary_insert_subset_diff_union_deleteVerts_incident
    {G : MultiGraph V E} {U : Set V} {v : V} (hvU : v ∉ U) :
    G.edgeBoundary (insert v U) ⊆
      ((G.edgeBoundary U) \ {e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e}) ∪
        {e : E | Incident (G.deleteVerts U) v e} := by
  classical
  intro e he
  rcases he with ⟨heG, x, y, hxy, hxIns, hyG, hyIns⟩
  have hyU : y ∉ U := by
    intro hy
    exact hyIns (Set.mem_insert_of_mem v hy)
  rcases Set.mem_insert_iff.mp hxIns with hxv | hxU
  · right
    subst x
    have hdelLink : (G.deleteVerts U).IsLink e v y := by
      rw [Graph.deleteVerts_isLink]
      exact ⟨hxy, hvU, hyU⟩
    exact ⟨hdelLink.edge_mem, hdelLink.inc_left⟩
  · left
    have heB : e ∈ G.edgeBoundary U := ⟨heG, x, y, hxy, hxU, hyG, hyU⟩
    refine ⟨heB, ?_⟩
    rintro ⟨_heB', hvInc⟩
    rcases hvInc.2.eq_or_eq_of_isLink hxy with hvx | hvy
    · exact hvU (hvx ▸ hxU)
    · exact hyIns (by
        rw [← hvy]
        exact Set.mem_insert v U)

lemma edgeBoundary_insert_ncard_lt_of_deleteVerts_degree_le_one
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : degree (G.deleteVerts U) v ≤ 1) :
    (G.edgeBoundary (insert v U)).ncard < (G.edgeBoundary U).ncard := by
  classical
  let B : Set E := G.edgeBoundary U
  let R : Set E := {e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e}
  let D : Set E := {e : E | Incident (G.deleteVerts U) v e}
  have hRsubB : R ⊆ B := by
    intro e he
    exact he.1
  have hRcard : 2 ≤ R.ncard := by
    simpa [R] using
      incident_boundary_ncard_ge_two_of_deleteVerts_degree_le_one
        (G := G) hCubic hv hvU hdeg
  have hDcard : D.ncard ≤ 1 := by
    simpa [D, deleteVerts_incident_set_ncard_eq_degree (G := G) U v] using hdeg
  have hsub :
      G.edgeBoundary (insert v U) ⊆ (B \ R) ∪ D := by
    simpa [B, R, D] using
      edgeBoundary_insert_subset_diff_union_deleteVerts_incident
        (G := G) (U := U) (v := v) hvU
  have hcardSub :
      (G.edgeBoundary (insert v U)).ncard ≤ ((B \ R) ∪ D).ncard :=
    Set.ncard_le_ncard hsub
  have hcardUnion :
      ((B \ R) ∪ D).ncard ≤ (B \ R).ncard + D.ncard :=
    Set.ncard_union_le (B \ R) D
  have hdiff : (B \ R).ncard = B.ncard - R.ncard := by
    rw [Set.ncard_diff hRsubB]
  have hRleB : R.ncard ≤ B.ncard := Set.ncard_le_ncard hRsubB
  have hnew_le :
      (G.edgeBoundary (insert v U)).ncard ≤ B.ncard - R.ncard + D.ncard := by
    exact hcardSub.trans (hcardUnion.trans (by rw [hdiff]))
  have hstrict : B.ncard - R.ncard + D.ncard < B.ncard := by
    omega
  exact hnew_le.trans_lt hstrict

lemma exists_pruned_superset_of_cycle_support
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    (C : G.CycleIn) :
    ∃ U : Set V,
      C.support ⊆ U ∧ U ⊆ G.vertexSet ∧
        (G.edgeBoundary U).ncard ≤ (G.edgeBoundary C.support).ncard ∧
          ∀ v : V, v ∈ G.vertexSet → v ∉ U →
            2 ≤ degree (G.deleteVerts U) v := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ U : Set V, C.support ⊆ U ∧ U ⊆ G.vertexSet ∧
      n = (G.edgeBoundary U).ncard
  have hP : ∃ n : ℕ, P n := by
    refine ⟨(G.edgeBoundary C.support).ncard, C.support, subset_rfl, ?_, rfl⟩
    exact C.support_subset_vertexSet
  let n₀ : ℕ := Nat.find hP
  obtain ⟨U, hCU, hUV, hUn⟩ := Nat.find_spec hP
  have hmin : ∀ W : Set V, C.support ⊆ W → W ⊆ G.vertexSet →
      (G.edgeBoundary U).ncard ≤ (G.edgeBoundary W).ncard := by
    intro W hCW hWV
    have hPW : P ((G.edgeBoundary W).ncard) := ⟨W, hCW, hWV, rfl⟩
    have hle : n₀ ≤ (G.edgeBoundary W).ncard := Nat.find_min' hP hPW
    simpa [n₀, hUn] using hle
  refine ⟨U, hCU, hUV, hmin C.support subset_rfl C.support_subset_vertexSet, ?_⟩
  intro v hvG hvU
  by_contra hnot
  have hdeg : degree (G.deleteVerts U) v ≤ 1 := by omega
  have hCinsert : C.support ⊆ insert v U := hCU.trans (Set.subset_insert v U)
  have hinsertV : insert v U ⊆ G.vertexSet := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxv | hxU
    · exact hxv ▸ hvG
    · exact hUV hxU
  have hlt :
      (G.edgeBoundary (insert v U)).ncard < (G.edgeBoundary U).ncard :=
    edgeBoundary_insert_ncard_lt_of_deleteVerts_degree_le_one
      (G := G) hCubic hvG hvU hdeg
  have hge :
      (G.edgeBoundary U).ncard ≤ (G.edgeBoundary (insert v U)).ncard :=
    hmin (insert v U) hCinsert hinsertV
  exact (not_lt_of_ge hge) hlt

lemma deleteVerts_degree_le_original_degree {G : MultiGraph V E}
    [Finite E] (U : Set V) (v : V) :
    degree (G.deleteVerts U) v ≤ G.degree v := by
  classical
  rw [← deleteVerts_incident_set_ncard_eq_degree (G := G) U v]
  change ({e : E | Incident (G.deleteVerts U) v e} : Set E).ncard ≤
    ({e : E | G.Incident v e} : Set E).ncard
  exact Set.ncard_le_ncard (deleteVerts_incident_subset_original (G := G) U v)

lemma deleteVerts_degree_le_three_of_cubic {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsCubic) {U : Set V} {v : V}
    (hv : v ∈ G.vertexSet) :
    degree (G.deleteVerts U) v ≤ 3 := by
  have hle := deleteVerts_degree_le_original_degree (G := G) U v
  have hdeg : G.degree v = 3 := hCubic.2 v hv
  omega

lemma incident_boundary_ncard_eq_one_of_deleteVerts_degree_eq_two
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : degree (G.deleteVerts U) v = 2) :
    ({e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e} : Set E).ncard = 1 := by
  classical
  let A : Set E := {e : E | G.Incident v e}
  let B : Set E := {e : E | Incident (G.deleteVerts U) v e}
  have hBA : B ⊆ A := deleteVerts_incident_subset_original (G := G) U v
  have hA : A.ncard = 3 := incident_edge_set_ncard_of_cubic (G := G) hCubic hv
  have hB : B.ncard = 2 := by
    rw [deleteVerts_incident_set_ncard_eq_degree (G := G) U v]
    exact hdeg
  have hdiff : (A \ B).ncard = 1 := by
    rw [Set.ncard_diff hBA]
    omega
  have hset :
      ({e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e} : Set E) = A \ B := by
    rw [incident_boundary_set_eq_original_not_deleteVerts (G := G) (U := U) (v := v) hvU]
    ext e
    rfl
  rw [hset]
  exact hdiff

private noncomputable def boundaryEdgeOfDeleteDegreeTwo {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsCubic) {U : Set V} {v : V}
    (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : degree (G.deleteVerts U) v = 2) :
    {e : E // e ∈ G.edgeBoundary U ∧ G.Incident v e} := by
  classical
  let S : Set E := {e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e}
  have hS : S.ncard = 1 := by
    simpa [S] using
      incident_boundary_ncard_eq_one_of_deleteVerts_degree_eq_two
        (G := G) hCubic hv hvU hdeg
  let hex : ∃ e : E, S = {e} := Set.ncard_eq_one.mp hS
  let e : E := Classical.choose hex
  have he : S = {e} := Classical.choose_spec hex
  exact ⟨e, by
    have hemem : e ∈ S := by
      rw [he]
      simp
    simpa [S] using hemem⟩

def degreeTwoOutsideSet (G : MultiGraph V E) [Finite E] (U : Set V) : Set V :=
  {v : V | v ∈ G.vertexSet ∧ v ∉ U ∧ degree (G.deleteVerts U) v = 2}

def branchVertexSet (G : MultiGraph V E) [Finite E] (U : Set V) : Set V :=
  {v : V | v ∈ G.vertexSet ∧ v ∉ U ∧ degree (G.deleteVerts U) v = 3}

lemma deleteVerts_vertexSet_ncard_eq_sub {G : MultiGraph V E}
    [Finite V] (U : Set V) (hUV : U ⊆ G.vertexSet) :
    (G.deleteVerts U).vertexSet.ncard = G.vertexSet.ncard - U.ncard := by
  rw [Graph.vertexSet_deleteVerts]
  exact Set.ncard_diff hUV

lemma deleteVerts_anti {G : MultiGraph V E} {X Y : Set V}
    (hXY : X ⊆ Y) :
    G.deleteVerts Y ≤ G.deleteVerts X := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [Graph.vertexSet_deleteVerts] at hv ⊢
    exact ⟨hv.1, fun hvX => hv.2 (hXY hvX)⟩
  · intro e x y hlink
    rw [Graph.deleteVerts_isLink] at hlink ⊢
    exact ⟨hlink.1, fun hx => hlink.2.1 (hXY hx),
      fun hy => hlink.2.2 (hXY hy)⟩

lemma cyclePackingTransfer_deleteVerts_of_subset {G : MultiGraph V E}
    {X Y : Set V} (hXY : X ⊆ Y) :
    CyclePackingTransfer (G.deleteVerts Y) (G.deleteVerts X) := by
  intro k hpack
  exact hasKDisjointCycles_of_subgraph (deleteVerts_anti (G := G) hXY) hpack

lemma degreeTwoOutside_ncard_le_edgeBoundary_ncard {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsCubic) (U : Set V) :
    (degreeTwoOutsideSet G U).ncard ≤ (G.edgeBoundary U).ncard := by
  classical
  let S : Set V := degreeTwoOutsideSet G U
  let f : S → G.edgeBoundary U := fun v =>
    ⟨(boundaryEdgeOfDeleteDegreeTwo (G := G) hCubic
      (U := U) (v := v.1) v.2.1 v.2.2.1 v.2.2.2).1,
      (boundaryEdgeOfDeleteDegreeTwo (G := G) hCubic
        (U := U) (v := v.1) v.2.1 v.2.2.1 v.2.2.2).2.1⟩
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    let ea := boundaryEdgeOfDeleteDegreeTwo (G := G) hCubic
      (U := U) (v := a.1) a.2.1 a.2.2.1 a.2.2.2
    let eb := boundaryEdgeOfDeleteDegreeTwo (G := G) hCubic
      (U := U) (v := b.1) b.2.1 b.2.2.1 b.2.2.2
    have heq : ea.1 = eb.1 := Subtype.ext_iff.mp hab
    have heaInc : G.Incident a.1 ea.1 := ea.2.2
    have hebInc : G.Incident b.1 ea.1 := by
      simpa [heq] using eb.2.2
    rcases ea.2.1 with ⟨heG, x, y, hxy, hxU, hyG, hyU⟩
    have haeq : a.1 = y := by
      rcases heaInc.2.eq_or_eq_of_isLink hxy with hax | hay
      · exact (a.2.2.1 (hax ▸ hxU)).elim
      · exact hay
    have hbeq : b.1 = y := by
      rcases hebInc.2.eq_or_eq_of_isLink hxy with hbx | hby
      · exact (b.2.2.1 (hbx ▸ hxU)).elim
      · exact hby
    exact haeq.trans hbeq.symm
  have hcard := Nat.card_le_card_of_injective f hfInjective
  simpa [S] using hcard

lemma deleteVerts_vertexSet_eq_degreeTwoOutside_union_branch
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsCubic)
    {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ degree (G.deleteVerts U) v) :
    (G.deleteVerts U).vertexSet =
      degreeTwoOutsideSet G U ∪ branchVertexSet G U := by
  ext v
  constructor
  · intro hv
    rw [Graph.vertexSet_deleteVerts] at hv
    have hge : 2 ≤ degree (G.deleteVerts U) v := hterminal v hv.1 hv.2
    have hle : degree (G.deleteVerts U) v ≤ 3 :=
      deleteVerts_degree_le_three_of_cubic (G := G) hCubic hv.1
    have hdeg : degree (G.deleteVerts U) v = 2 ∨
        degree (G.deleteVerts U) v = 3 := by omega
    rcases hdeg with hdeg | hdeg
    · left
      exact ⟨hv.1, hv.2, hdeg⟩
    · right
      exact ⟨hv.1, hv.2, hdeg⟩
  · rintro (hv | hv)
    · rw [Graph.vertexSet_deleteVerts]
      exact ⟨hv.1, hv.2.1⟩
    · rw [Graph.vertexSet_deleteVerts]
      exact ⟨hv.1, hv.2.1⟩

lemma degreeTwoOutside_disjoint_branch {G : MultiGraph V E}
    [Finite E] (U : Set V) :
    Disjoint (degreeTwoOutsideSet G U) (branchVertexSet G U) := by
  rw [Set.disjoint_left]
  intro v hv2 hv3
  rcases hv2 with ⟨_hvG2, _hvU2, hdeg2⟩
  rcases hv3 with ⟨_hvG3, _hvU3, hdeg3⟩
  omega

lemma branchVertexSet_ncard_ge_sub_two_cycle
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsCubic)
    (C : G.CycleIn) {U : Set V} (hUV : U ⊆ G.vertexSet)
    (hscore : U.ncard + (G.edgeBoundary U).ncard ≤
      C.support.ncard + (G.edgeBoundary C.support).ncard)
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ degree (G.deleteVerts U) v) :
    G.vertexSet.ncard - 2 * C.support.ncard ≤
      (branchVertexSet G U).ncard := by
  classical
  let D₂ : Set V := degreeTwoOutsideSet G U
  let B₃ : Set V := branchVertexSet G U
  have hR_eq :
      (G.deleteVerts U).vertexSet = D₂ ∪ B₃ := by
    simpa [D₂, B₃] using
      deleteVerts_vertexSet_eq_degreeTwoOutside_union_branch
        (G := G) hCubic (U := U) hterminal
  have hdisj : Disjoint D₂ B₃ := by
    simpa [D₂, B₃] using degreeTwoOutside_disjoint_branch (G := G) U
  have hRcard :
      (G.deleteVerts U).vertexSet.ncard = D₂.ncard + B₃.ncard := by
    rw [hR_eq, Set.ncard_union_eq hdisj]
  have hD₂le : D₂.ncard ≤ (G.edgeBoundary U).ncard := by
    simpa [D₂] using degreeTwoOutside_ncard_le_edgeBoundary_ncard (G := G) hCubic U
  have hboundaryC : (G.edgeBoundary C.support).ncard ≤ C.support.ncard :=
    edgeBoundary_ncard_le_cycle_support_ncard (G := G) hCubic C
  have hUD₂le : U.ncard + D₂.ncard ≤ 2 * C.support.ncard := by
    omega
  have hdel :
      (G.deleteVerts U).vertexSet.ncard = G.vertexSet.ncard - U.ncard :=
    deleteVerts_vertexSet_ncard_eq_sub (G := G) U hUV
  change G.vertexSet.ncard - 2 * C.support.ncard ≤ B₃.ncard
  omega

lemma edgeBoundary_insert_score_le_of_deleteVerts_degree_le_one
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : degree (G.deleteVerts U) v ≤ 1) :
    (insert v U).ncard + (G.edgeBoundary (insert v U)).ncard ≤
      U.ncard + (G.edgeBoundary U).ncard := by
  classical
  have hboundary_lt :
      (G.edgeBoundary (insert v U)).ncard < (G.edgeBoundary U).ncard :=
    edgeBoundary_insert_ncard_lt_of_deleteVerts_degree_le_one
      (G := G) hCubic hv hvU hdeg
  have hboundary_succ :
      (G.edgeBoundary (insert v U)).ncard + 1 ≤ (G.edgeBoundary U).ncard := by
    omega
  have hinsert : (insert v U).ncard = U.ncard + 1 := by
    rw [Set.ncard_insert_of_notMem hvU]
  omega

lemma exists_pruned_superset_of_cycle_support_with_score
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsCubic)
    (C : G.CycleIn) :
    ∃ U : Set V,
      C.support ⊆ U ∧ U ⊆ G.vertexSet ∧
        U.ncard + (G.edgeBoundary U).ncard ≤
          C.support.ncard + (G.edgeBoundary C.support).ncard ∧
          ∀ v : V, v ∈ G.vertexSet → v ∉ U →
            2 ≤ degree (G.deleteVerts U) v := by
  classical
  let scoreBound : ℕ := C.support.ncard + (G.edgeBoundary C.support).ncard
  let good : ℕ → Prop := fun n =>
    ∃ U : Set V, C.support ⊆ U ∧ U ⊆ G.vertexSet ∧
      U.ncard + (G.edgeBoundary U).ncard ≤ scoreBound ∧ U.ncard = n
  letI : DecidablePred good := Classical.decPred good
  let bound : ℕ := G.vertexSet.ncard
  have hgood0 : good C.support.ncard := by
    refine ⟨C.support, subset_rfl, C.support_subset_vertexSet, ?_, rfl⟩
    exact le_rfl
  have hCbound : C.support.ncard ≤ bound := by
    exact Set.ncard_le_ncard C.support_subset_vertexSet
  have hgoodMax : good (Nat.findGreatest good bound) :=
    Nat.findGreatest_spec (P := good) (n := bound) hCbound hgood0
  rcases hgoodMax with ⟨U, hCU, hUV, hscore, hUmax⟩
  refine ⟨U, hCU, hUV, hscore, ?_⟩
  intro v hvG hvU
  by_contra hnot
  have hdeg : degree (G.deleteVerts U) v ≤ 1 := by omega
  have hCinsert : C.support ⊆ insert v U := hCU.trans (Set.subset_insert v U)
  have hinsertV : insert v U ⊆ G.vertexSet := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxv | hxU
    · exact hxv ▸ hvG
    · exact hUV hxU
  have hscoreInsert :
      (insert v U).ncard + (G.edgeBoundary (insert v U)).ncard ≤ scoreBound := by
    exact (edgeBoundary_insert_score_le_of_deleteVerts_degree_le_one
      (G := G) hCubic hvG hvU hdeg).trans hscore
  have hinsertCard : (insert v U).ncard = U.ncard + 1 := by
    rw [Set.ncard_insert_of_notMem hvU]
  have hgoodInsert : good (insert v U).ncard :=
    ⟨insert v U, hCinsert, hinsertV, hscoreInsert, rfl⟩
  have hinsertBound : (insert v U).ncard ≤ bound :=
    Set.ncard_le_ncard hinsertV
  have hfind_lt : Nat.findGreatest good bound < (insert v U).ncard := by
    rw [← hUmax, hinsertCard]
    omega
  exact (Nat.findGreatest_is_greatest (P := good) (n := bound)
    hfind_lt hinsertBound) hgoodInsert

lemma pruned_score_ncard_le_two_cycle_support {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsCubic) (C : G.CycleIn)
    {U : Set V}
    (hscore : U.ncard + (G.edgeBoundary U).ncard ≤
      C.support.ncard + (G.edgeBoundary C.support).ncard) :
    U.ncard ≤ 2 * C.support.ncard := by
  have hboundary : (G.edgeBoundary C.support).ncard ≤ C.support.ncard :=
    edgeBoundary_ncard_le_cycle_support_ncard (G := G) hCubic C
  omega

lemma deleteVerts_pruned_vertexSet_ncard_ge_sub_two_cycle
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsCubic)
    (C : G.CycleIn) {U : Set V} (hUV : U ⊆ G.vertexSet)
    (hscore : U.ncard + (G.edgeBoundary U).ncard ≤
      C.support.ncard + (G.edgeBoundary C.support).ncard) :
    G.vertexSet.ncard - 2 * C.support.ncard ≤
      (G.deleteVerts U).vertexSet.ncard := by
  have hUle : U.ncard ≤ 2 * C.support.ncard :=
    pruned_score_ncard_le_two_cycle_support (G := G) hCubic C hscore
  have hdel := deleteVerts_vertexSet_ncard_eq_sub (G := G) U hUV
  rw [hdel]
  omega

end MultiGraph

end Chapter02
end Diestel
