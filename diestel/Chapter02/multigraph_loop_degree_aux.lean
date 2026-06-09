import Chapter02.cycle_packing_analytic_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

/-- Loops at a vertex, as a set of edge labels. -/
def loopSetAt (G : MultiGraph V E) (v : V) : Set E :=
  {e : E | e ∈ G.edgeSet ∧ G.IsLoopAt e v}

/--
Diestel's multigraph degree: an ordinary incident edge contributes once,
and a loop contributes twice. Since `Graph.Inc` counts a loop once, we add
the loop set once more.
-/
noncomputable def diestelDegree (G : MultiGraph V E) [Finite E] (v : V) : ℕ :=
  Nat.card {e : E // G.Incident v e} + Nat.card {e : E // e ∈ G.loopSetAt v}

/-- `G` is regular of degree `k` in Diestel's multigraph sense. -/
def IsDiestelRegularOfDegree (G : MultiGraph V E) [Finite E] (k : ℕ) : Prop :=
  ∀ v : V, v ∈ G.vertexSet → G.diestelDegree v = k

/-- A cubic multigraph in Diestel's sense: loops are allowed and count twice. -/
abbrev IsDiestelCubic (G : MultiGraph V E) [Finite E] : Prop :=
  G.IsDiestelRegularOfDegree 3

lemma loopSetAt_subset_incident {G : MultiGraph V E} (v : V) :
    G.loopSetAt v ⊆ {e : E | G.Incident v e} := by
  intro e he
  exact ⟨he.1, he.2.inc⟩

lemma loopSetAt_eq_empty_of_loopless {G : MultiGraph V E}
    (hG : G.Loopless) (v : V) :
    G.loopSetAt v = ∅ := by
  ext e
  constructor
  · intro he
    exact (hG he.1 v he.2).elim
  · intro he
    simp at he

lemma diestelDegree_eq_degree_of_loopless {G : MultiGraph V E}
    [Finite E] (hG : G.Loopless) (v : V) :
    G.diestelDegree v = G.degree v := by
  simp [diestelDegree, degree, loopSetAt_eq_empty_of_loopless (G := G) hG v]

lemma isDiestelCubic_of_isCubic {G : MultiGraph V E}
    [Finite E] (hG : G.IsCubic) :
    G.IsDiestelCubic := by
  intro v hv
  rw [diestelDegree_eq_degree_of_loopless (G := G) hG.1 v]
  exact hG.2 v hv

lemma isCubic_of_isDiestelCubic_of_loopless {G : MultiGraph V E}
    [Finite E] (hloopless : G.Loopless) (hG : G.IsDiestelCubic) :
    G.IsCubic := by
  refine ⟨hloopless, ?_⟩
  intro v hv
  have hdeg := hG v hv
  rwa [diestelDegree_eq_degree_of_loopless (G := G) hloopless v] at hdeg

lemma loopless_of_no_loop {G : MultiGraph V E}
    (h : ¬ ∃ e : E, ∃ v : V, G.IsLoopAt e v) :
    G.Loopless := by
  intro e _he x hloop
  exact h ⟨e, x, hloop⟩

/-- A selected edge set has Diestel-degree `k` at `v`, with loops counted twice. -/
noncomputable def diestelDegreeInEdgeSet
    (G : MultiGraph V E) (F : Set E) (v : V) : ℕ :=
  Nat.card {e : F // G.Inc e.1 v} +
    Nat.card {e : F // G.IsLoopAt e.1 v}

/-- The selected-edge tokens counted by Diestel degree in an edge set. -/
abbrev DegreeTokenInEdgeSet (G : MultiGraph V E) (F : Set E) (v : V) :=
  {e : F // G.Inc e.1 v} ⊕ {e : F // G.IsLoopAt e.1 v}

lemma diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
    (G : MultiGraph V E) (F : Set E) (v : V) (hF : F.Finite) :
    G.diestelDegreeInEdgeSet F v =
      Nat.card (DegreeTokenInEdgeSet G F v) := by
  haveI : Finite F := Set.Finite.to_subtype hF
  rw [DegreeTokenInEdgeSet, diestelDegreeInEdgeSet, Nat.card_sum]

/--
The two kinds of tokens counted by Diestel degree at a vertex: one incidence
token for every incident edge, and one extra token for every loop.
-/
abbrev DegreeToken (G : MultiGraph V E) (v : V) :=
  {e : E // G.Incident v e} ⊕ {e : E // e ∈ G.loopSetAt v}

lemma diestelDegree_eq_card_degreeToken (G : MultiGraph V E) [Finite E] (v : V) :
    G.diestelDegree v = Nat.card (DegreeToken G v) := by
  rw [DegreeToken, Nat.card_sum]
  rfl

/--
A cycle in a multigraph in Diestel's sense, represented as a connected
2-regular edge set with loops counted twice.
-/
structure DiestelCycleIn (G : MultiGraph V E) where
  support : Set V
  edgeSupport : Set E
  edgeSupport_finite : edgeSupport.Finite
  edges_inside : edgeSupport ⊆ G.EdgeSetInside support
  support_nonempty : support.Nonempty
  connected : ((G.edgeSubgraph edgeSupport).induce support).Connected
  degree_two : ∀ v : V, v ∈ support →
    diestelDegreeInEdgeSet G edgeSupport v = 2

/-- `G` contains `k` pairwise vertex-disjoint Diestel multigraph cycles. -/
def HasKDisjointDiestelCycles (G : MultiGraph V E) (k : ℕ) : Prop :=
  ∃ C : Fin k → DiestelCycleIn G, Pairwise fun i j => Disjoint (C i).support (C j).support

/-- A loopless multigraph cycle is a Diestel cycle, since there are no loops to count twice. -/
def DiestelCycleIn.ofCycleIn_of_loopless {G : MultiGraph V E}
    (hloopless : G.Loopless) (C : G.CycleIn) : G.DiestelCycleIn where
  support := C.support
  edgeSupport := C.edgeSupport
  edgeSupport_finite := C.edgeSupport_finite
  edges_inside := C.edges_inside
  support_nonempty := C.support_nonempty
  connected := C.connected
  degree_two := by
    intro v hv
    have hnoLoop : IsEmpty {e : C.edgeSupport // G.IsLoopAt e.1 v} := by
      refine ⟨?_⟩
      intro e
      exact hloopless e.2.edge_mem v e.2
    simp [diestelDegreeInEdgeSet, C.degree_two v hv]

lemma hasKDisjointDiestelCycles_of_hasKDisjointCycles_of_loopless
    {G : MultiGraph V E} {k : ℕ} (hloopless : G.Loopless) :
    G.HasKDisjointCycles k → G.HasKDisjointDiestelCycles k := by
  rintro ⟨C, hpair⟩
  refine ⟨fun i => DiestelCycleIn.ofCycleIn_of_loopless (G := G) hloopless (C i), ?_⟩
  simpa [DiestelCycleIn.ofCycleIn_of_loopless] using hpair

/-- In a loopless multigraph, a Diestel cycle is an ordinary multigraph cycle. -/
def CycleIn.ofDiestelCycleIn_of_loopless {G : MultiGraph V E}
    (hloopless : G.Loopless) (C : G.DiestelCycleIn) : G.CycleIn where
  support := C.support
  edgeSupport := C.edgeSupport
  edgeSupport_finite := C.edgeSupport_finite
  edges_inside := C.edges_inside
  support_nonempty := C.support_nonempty
  connected := C.connected
  degree_two := by
    intro v hv
    have hdeg := C.degree_two v hv
    have hnoLoop : IsEmpty {e : C.edgeSupport // G.IsLoopAt e.1 v} := by
      refine ⟨?_⟩
      intro e
      exact hloopless e.2.edge_mem v e.2
    change Nat.card {e : C.edgeSupport // G.Inc e.1 v} = 2
    rw [← hdeg]
    simp [diestelDegreeInEdgeSet]

lemma hasKDisjointCycles_of_hasKDisjointDiestelCycles_of_loopless
    {G : MultiGraph V E} {k : ℕ} (hloopless : G.Loopless) :
    G.HasKDisjointDiestelCycles k → G.HasKDisjointCycles k := by
  rintro ⟨C, hpair⟩
  refine ⟨fun i => CycleIn.ofDiestelCycleIn_of_loopless (G := G) hloopless (C i), ?_⟩
  simpa [CycleIn.ofDiestelCycleIn_of_loopless] using hpair

lemma diestelCycle_support_subset_vertexSet {G : MultiGraph V E}
    (C : G.DiestelCycleIn) :
    C.support ⊆ G.vertexSet := by
  intro v hv
  have hcard := C.degree_two v hv
  have hsum_eq :
      Nat.card {e : C.edgeSupport // G.Inc e.1 v} +
        Nat.card {e : C.edgeSupport // G.IsLoopAt e.1 v} = 2 := by
    simpa [diestelDegreeInEdgeSet] using hcard
  have hsum_pos :
      0 < Nat.card {e : C.edgeSupport // G.Inc e.1 v} +
        Nat.card {e : C.edgeSupport // G.IsLoopAt e.1 v} := by
    omega
  have hleft_or :
      0 < Nat.card {e : C.edgeSupport // G.Inc e.1 v} ∨
        0 < Nat.card {e : C.edgeSupport // G.IsLoopAt e.1 v} := by
    omega
  rcases hleft_or with hleft | hloop
  · haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
    haveI : Finite {e : C.edgeSupport // G.Inc e.1 v} := inferInstance
    rcases (Finite.card_pos_iff.mp hleft : Nonempty {e : C.edgeSupport // G.Inc e.1 v}) with ⟨e⟩
    exact e.2.vertex_mem
  · haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
    haveI : Finite {e : C.edgeSupport // G.IsLoopAt e.1 v} := inferInstance
    rcases (Finite.card_pos_iff.mp hloop :
      Nonempty {e : C.edgeSupport // G.IsLoopAt e.1 v}) with ⟨e⟩
    exact e.2.vertex_mem

lemma diestel_incident_add_loop_ncard_of_cubic {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsDiestelCubic) {v : V} (hv : v ∈ G.vertexSet) :
    ({e : E | G.Incident v e} : Set E).ncard +
      (G.loopSetAt v).ncard = 3 := by
  change Nat.card {e : E // G.Incident v e} +
      Nat.card {e : E // e ∈ G.loopSetAt v} = 3
  exact hCubic v hv

lemma diestelCycle_incident_add_loop_ncard {G : MultiGraph V E}
    (C : G.DiestelCycleIn) {v : V} (hv : v ∈ C.support) :
    ({e : E | e ∈ C.edgeSupport ∧ G.Inc e v} : Set E).ncard +
      ({e : E | e ∈ C.edgeSupport ∧ G.IsLoopAt e v} : Set E).ncard = 2 := by
  classical
  let φInc :
      {e : C.edgeSupport // G.Inc e.1 v} ≃
        {e : E // e ∈ C.edgeSupport ∧ G.Inc e v} :=
    { toFun := fun e => ⟨e.1.1, e.1.2, e.2⟩
      invFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  let φLoop :
      {e : C.edgeSupport // G.IsLoopAt e.1 v} ≃
        {e : E // e ∈ C.edgeSupport ∧ G.IsLoopAt e v} :=
    { toFun := fun e => ⟨e.1.1, e.1.2, e.2⟩
      invFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  change Nat.card {e : E // e ∈ C.edgeSupport ∧ G.Inc e v} +
      Nat.card {e : E // e ∈ C.edgeSupport ∧ G.IsLoopAt e v} = 2
  rw [← Nat.card_congr φInc, ← Nat.card_congr φLoop]
  exact C.degree_two v hv

private lemma diestel_edgeBoundary_not_mem_cycle_edgeSupport {G : MultiGraph V E}
    (C : G.DiestelCycleIn) (e : G.edgeBoundary C.support) :
    e.1 ∉ C.edgeSupport := by
  intro heC
  rcases e.2 with ⟨_heG, x, y, hxy, _hxC, _hyG, hyC⟩
  exact hyC ((C.edges_inside heC).2 y hxy.inc_right)

lemma diestel_boundary_incident_ncard_le_one {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsDiestelCubic) (C : G.DiestelCycleIn)
    {v : V} (hv : v ∈ C.support) :
    ({e : E | e ∈ G.edgeBoundary C.support ∧ G.Incident v e} : Set E).ncard ≤ 1 := by
  classical
  let A : Set E := {e : E | G.Incident v e}
  let B : Set E := {e : E | e ∈ C.edgeSupport ∧ G.Inc e v}
  let L : Set E := G.loopSetAt v
  let LC : Set E := {e : E | e ∈ C.edgeSupport ∧ G.IsLoopAt e v}
  have hBA : B ⊆ A := by
    intro e he
    exact ⟨(C.edges_inside he.1).1, he.2⟩
  have hLCL : LC ⊆ L := by
    intro e he
    exact ⟨he.2.edge_mem, he.2⟩
  have hAplusL : A.ncard + L.ncard = 3 := by
    simpa [A, L] using
      diestel_incident_add_loop_ncard_of_cubic (G := G) hCubic
        (diestelCycle_support_subset_vertexSet (G := G) C hv)
  have hBplusLC : B.ncard + LC.ncard = 2 := by
    simpa [B, LC] using diestelCycle_incident_add_loop_ncard (G := G) C hv
  have hLCleL : LC.ncard ≤ L.ncard := Set.ncard_le_ncard hLCL
  have hdiff_le : A.ncard - B.ncard ≤ 1 := by
    omega
  let R : Set E := {e : E | e ∈ G.edgeBoundary C.support ∧ G.Incident v e}
  have hRsub : R ⊆ A \ B := by
    intro e he
    refine ⟨he.2, ?_⟩
    intro heB
    exact diestel_edgeBoundary_not_mem_cycle_edgeSupport (G := G) C
      ⟨e, he.1⟩ heB.1
  have hRle : R.ncard ≤ (A \ B).ncard := Set.ncard_le_ncard hRsub
  have hdiff : (A \ B).ncard = A.ncard - B.ncard := by
    rw [Set.ncard_diff hBA]
  have hdiff_le' : (A \ B).ncard ≤ 1 := by
    rw [hdiff]
    exact hdiff_le
  simpa [R] using hRle.trans hdiff_le'

private noncomputable def diestelEdgeBoundaryInsideEndpoint {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) : U :=
  ⟨Classical.choose e.2.2,
    (Classical.choose_spec (Classical.choose_spec e.2.2)).2.1⟩

private lemma diestelEdgeBoundaryInsideEndpoint_isLink {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) :
    G.IsLink e.1 (diestelEdgeBoundaryInsideEndpoint (G := G) U e).1
      (Classical.choose (Classical.choose_spec e.2.2)) := by
  exact (Classical.choose_spec (Classical.choose_spec e.2.2)).1

private lemma diestelEdgeBoundaryInsideEndpoint_inc {G : MultiGraph V E}
    (U : Set V) (e : G.edgeBoundary U) :
    G.Inc e.1 (diestelEdgeBoundaryInsideEndpoint (G := G) U e).1 :=
  (diestelEdgeBoundaryInsideEndpoint_isLink (G := G) U e).inc_left

private lemma diestel_boundary_edge_mem_incident_set {G : MultiGraph V E}
    (C : G.DiestelCycleIn) (e : G.edgeBoundary C.support) :
    e.1 ∈
      ({f : E | f ∈ G.edgeBoundary C.support ∧
        G.Incident (diestelEdgeBoundaryInsideEndpoint (G := G) C.support e).1 f} :
          Set E) := by
  exact ⟨e.2, ⟨e.2.1, diestelEdgeBoundaryInsideEndpoint_inc (G := G) C.support e⟩⟩

lemma diestelEdgeBoundaryInsideEndpoint_injective {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsDiestelCubic) (C : G.DiestelCycleIn) :
    Function.Injective
      (diestelEdgeBoundaryInsideEndpoint (G := G) C.support) := by
  intro e f hef
  have hv :
      (diestelEdgeBoundaryInsideEndpoint (G := G) C.support e).1 ∈ C.support :=
    (diestelEdgeBoundaryInsideEndpoint (G := G) C.support e).2
  let S : Set E :=
    {g : E | g ∈ G.edgeBoundary C.support ∧
      G.Incident (diestelEdgeBoundaryInsideEndpoint (G := G) C.support e).1 g}
  have hSle : S.ncard ≤ 1 := by
    simpa [S] using
      diestel_boundary_incident_ncard_le_one (G := G) hCubic C hv
  have heS : e.1 ∈ S :=
    diestel_boundary_edge_mem_incident_set (G := G) C e
  have hfS : f.1 ∈ S := by
    have hfS' :
        f.1 ∈
          ({g : E | g ∈ G.edgeBoundary C.support ∧
            G.Incident
              (diestelEdgeBoundaryInsideEndpoint (G := G) C.support f).1 g} :
            Set E) :=
      diestel_boundary_edge_mem_incident_set (G := G) C f
    simpa [S, hef] using hfS'
  exact Subtype.ext (((Set.ncard_le_one (s := S)).mp hSle) e.1 heS f.1 hfS)

lemma diestel_edgeBoundary_ncard_le_cycle_support_ncard {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsDiestelCubic)
    (C : G.DiestelCycleIn) :
    (G.edgeBoundary C.support).ncard ≤ C.support.ncard := by
  classical
  have hinj := diestelEdgeBoundaryInsideEndpoint_injective (G := G) hCubic C
  have hcard :=
    Nat.card_le_card_of_injective
      (diestelEdgeBoundaryInsideEndpoint (G := G) C.support) hinj
  simpa using hcard

lemma deleteVerts_loopSetAt_eq_of_not_mem {G : MultiGraph V E}
    {U : Set V} {v : V} (hvU : v ∉ U) :
    loopSetAt (G.deleteVerts U : MultiGraph V E) v = G.loopSetAt v := by
  ext e
  constructor
  · intro he
    exact ⟨(Graph.deleteVerts_le (G := G) (X := U)).edgeSet_mono he.1,
      he.2.mono (Graph.deleteVerts_le (G := G) (X := U))⟩
  · intro he
    have hloop : (G.deleteVerts U).IsLoopAt e v := by
      change (G.deleteVerts U).IsLink e v v
      rw [Graph.deleteVerts_isLink]
      exact ⟨he.2, hvU, hvU⟩
    exact ⟨hloop.edge_mem, hloop⟩

lemma deleteVerts_diestelDegree_le_original_diestelDegree {G : MultiGraph V E}
    [Finite E] (U : Set V) (v : V) :
    diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ G.diestelDegree v := by
  classical
  have hIle :
      ({e : E | Incident (G.deleteVerts U) v e} : Set E).ncard ≤
        ({e : E | G.Incident v e} : Set E).ncard :=
    Set.ncard_le_ncard (deleteVerts_incident_subset_original (G := G) U v)
  have hLle :
      (loopSetAt (G.deleteVerts U : MultiGraph V E) v).ncard ≤
        (G.loopSetAt v).ncard := by
    refine Set.ncard_le_ncard ?_
    intro e he
    exact ⟨(Graph.deleteVerts_le (G := G) (X := U)).edgeSet_mono he.1,
      he.2.mono (Graph.deleteVerts_le (G := G) (X := U))⟩
  change
    ({e : E | Incident (G.deleteVerts U) v e} : Set E).ncard +
        (loopSetAt (G.deleteVerts U : MultiGraph V E) v).ncard ≤
      ({e : E | G.Incident v e} : Set E).ncard + (G.loopSetAt v).ncard
  omega

lemma deleteVerts_diestelDegree_le_three_of_cubic {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsDiestelCubic) {U : Set V} {v : V}
    (hv : v ∈ G.vertexSet) :
    diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 3 := by
  have hle := deleteVerts_diestelDegree_le_original_diestelDegree (G := G) U v
  have hdeg : G.diestelDegree v = 3 := hCubic v hv
  omega

lemma original_incident_not_deleteVerts_ncard_ge_two_of_diestelDegree_le_one
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 1) :
    2 ≤ ({e : E | G.Incident v e ∧ ¬ Incident (G.deleteVerts U) v e} :
      Set E).ncard := by
  classical
  let A : Set E := {e : E | G.Incident v e}
  let B : Set E := {e : E | Incident (G.deleteVerts U) v e}
  let L : Set E := G.loopSetAt v
  have hBA : B ⊆ A := deleteVerts_incident_subset_original (G := G) U v
  have hAplusL : A.ncard + L.ncard = 3 := by
    simpa [A, L] using diestel_incident_add_loop_ncard_of_cubic (G := G) hCubic hv
  have hBplusL : B.ncard + L.ncard ≤ 1 := by
    simpa [B, L, diestelDegree, deleteVerts_loopSetAt_eq_of_not_mem (G := G) hvU] using hdeg
  have hdiff : 2 ≤ (A \ B).ncard := by
    rw [Set.ncard_diff hBA]
    omega
  have hset :
      ({e : E | G.Incident v e ∧ ¬ Incident (G.deleteVerts U) v e} :
        Set E) = A \ B := by
    ext e
    rfl
  rw [hset]
  exact hdiff

lemma incident_boundary_ncard_ge_two_of_deleteVerts_diestelDegree_le_one
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 1) :
    2 ≤ ({e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e} : Set E).ncard := by
  rw [incident_boundary_set_eq_original_not_deleteVerts (G := G) (U := U) (v := v) hvU]
  exact original_incident_not_deleteVerts_ncard_ge_two_of_diestelDegree_le_one
    (G := G) hCubic hv hvU hdeg

lemma edgeBoundary_insert_ncard_lt_of_deleteVerts_diestelDegree_le_one
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 1) :
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
      incident_boundary_ncard_ge_two_of_deleteVerts_diestelDegree_le_one
        (G := G) hCubic hv hvU hdeg
  have hDcard : D.ncard ≤ 1 := by
    have h :
        D.ncard + (loopSetAt (G.deleteVerts U : MultiGraph V E) v).ncard ≤ 1 := by
      simpa [D, diestelDegree] using hdeg
    omega
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

lemma edgeBoundary_insert_score_le_of_deleteVerts_diestelDegree_le_one
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 1) :
    (insert v U).ncard + (G.edgeBoundary (insert v U)).ncard ≤
      U.ncard + (G.edgeBoundary U).ncard := by
  classical
  have hboundary_lt :
      (G.edgeBoundary (insert v U)).ncard < (G.edgeBoundary U).ncard :=
    edgeBoundary_insert_ncard_lt_of_deleteVerts_diestelDegree_le_one
      (G := G) hCubic hv hvU hdeg
  have hboundary_succ :
      (G.edgeBoundary (insert v U)).ncard + 1 ≤ (G.edgeBoundary U).ncard := by
    omega
  have hinsert : (insert v U).ncard = U.ncard + 1 := by
    rw [Set.ncard_insert_of_notMem hvU]
  omega

lemma exists_pruned_superset_of_diestelCycle_support_with_score
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsDiestelCubic)
    (C : G.DiestelCycleIn) :
    ∃ U : Set V,
      C.support ⊆ U ∧ U ⊆ G.vertexSet ∧
        U.ncard + (G.edgeBoundary U).ncard ≤
          C.support.ncard + (G.edgeBoundary C.support).ncard ∧
          ∀ v : V, v ∈ G.vertexSet → v ∉ U →
            2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v := by
  classical
  let scoreBound : ℕ := C.support.ncard + (G.edgeBoundary C.support).ncard
  let good : ℕ → Prop := fun n =>
    ∃ U : Set V, C.support ⊆ U ∧ U ⊆ G.vertexSet ∧
      U.ncard + (G.edgeBoundary U).ncard ≤ scoreBound ∧ U.ncard = n
  letI : DecidablePred good := Classical.decPred good
  let bound : ℕ := G.vertexSet.ncard
  have hgood0 : good C.support.ncard := by
    refine ⟨C.support, subset_rfl, diestelCycle_support_subset_vertexSet (G := G) C, ?_, rfl⟩
    exact le_rfl
  have hCbound : C.support.ncard ≤ bound := by
    exact Set.ncard_le_ncard (diestelCycle_support_subset_vertexSet (G := G) C)
  have hgoodMax : good (Nat.findGreatest good bound) :=
    Nat.findGreatest_spec (P := good) (n := bound) hCbound hgood0
  rcases hgoodMax with ⟨U, hCU, hUV, hscore, hUmax⟩
  refine ⟨U, hCU, hUV, hscore, ?_⟩
  intro v hvG hvU
  by_contra hnot
  have hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 1 := by omega
  have hCinsert : C.support ⊆ insert v U := hCU.trans (Set.subset_insert v U)
  have hinsertV : insert v U ⊆ G.vertexSet := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxv | hxU
    · exact hxv ▸ hvG
    · exact hUV hxU
  have hscoreInsert :
      (insert v U).ncard + (G.edgeBoundary (insert v U)).ncard ≤ scoreBound := by
    exact (edgeBoundary_insert_score_le_of_deleteVerts_diestelDegree_le_one
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

lemma diestel_pruned_score_ncard_le_two_cycle_support {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsDiestelCubic) (C : G.DiestelCycleIn)
    {U : Set V}
    (hscore : U.ncard + (G.edgeBoundary U).ncard ≤
      C.support.ncard + (G.edgeBoundary C.support).ncard) :
    U.ncard ≤ 2 * C.support.ncard := by
  have hboundary : (G.edgeBoundary C.support).ncard ≤ C.support.ncard :=
    diestel_edgeBoundary_ncard_le_cycle_support_ncard (G := G) hCubic C
  omega

lemma deleteVerts_diestelPruned_vertexSet_ncard_ge_sub_two_cycle
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsDiestelCubic)
    (C : G.DiestelCycleIn) {U : Set V} (hUV : U ⊆ G.vertexSet)
    (hscore : U.ncard + (G.edgeBoundary U).ncard ≤
      C.support.ncard + (G.edgeBoundary C.support).ncard) :
    G.vertexSet.ncard - 2 * C.support.ncard ≤
      (G.deleteVerts U).vertexSet.ncard := by
  have hUle : U.ncard ≤ 2 * C.support.ncard :=
    diestel_pruned_score_ncard_le_two_cycle_support (G := G) hCubic C hscore
  have hdel := deleteVerts_vertexSet_ncard_eq_sub (G := G) U hUV
  rw [hdel]
  omega

lemma incident_boundary_ncard_eq_one_of_deleteVerts_diestelDegree_eq_two
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V} {v : V} (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v = 2) :
    ({e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e} : Set E).ncard = 1 := by
  classical
  let A : Set E := {e : E | G.Incident v e}
  let B : Set E := {e : E | Incident (G.deleteVerts U) v e}
  let L : Set E := G.loopSetAt v
  have hBA : B ⊆ A := deleteVerts_incident_subset_original (G := G) U v
  have hAplusL : A.ncard + L.ncard = 3 := by
    simpa [A, L] using diestel_incident_add_loop_ncard_of_cubic (G := G) hCubic hv
  have hBplusL : B.ncard + L.ncard = 2 := by
    simpa [B, L, diestelDegree, deleteVerts_loopSetAt_eq_of_not_mem (G := G) hvU] using hdeg
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

private noncomputable def boundaryEdgeOfDeleteDiestelDegreeTwo {G : MultiGraph V E}
    [Finite E] (hCubic : G.IsDiestelCubic) {U : Set V} {v : V}
    (hv : v ∈ G.vertexSet) (hvU : v ∉ U)
    (hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v = 2) :
    {e : E // e ∈ G.edgeBoundary U ∧ G.Incident v e} := by
  classical
  let S : Set E := {e : E | e ∈ G.edgeBoundary U ∧ G.Incident v e}
  have hS : S.ncard = 1 := by
    simpa [S] using
      incident_boundary_ncard_eq_one_of_deleteVerts_diestelDegree_eq_two
        (G := G) hCubic hv hvU hdeg
  let hex : ∃ e : E, S = {e} := Set.ncard_eq_one.mp hS
  let e : E := Classical.choose hex
  have he : S = {e} := Classical.choose_spec hex
  exact ⟨e, by
    have hemem : e ∈ S := by
      rw [he]
      simp
    simpa [S] using hemem⟩

def diestelDegreeTwoOutsideSet (G : MultiGraph V E) [Finite E] (U : Set V) : Set V :=
  {v : V | v ∈ G.vertexSet ∧ v ∉ U ∧
    diestelDegree (G.deleteVerts U : MultiGraph V E) v = 2}

def diestelBranchVertexSet (G : MultiGraph V E) [Finite E] (U : Set V) : Set V :=
  {v : V | v ∈ G.vertexSet ∧ v ∉ U ∧
    diestelDegree (G.deleteVerts U : MultiGraph V E) v = 3}

lemma diestelDegreeTwoOutside_ncard_le_edgeBoundary_ncard {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsDiestelCubic) (U : Set V) :
    (diestelDegreeTwoOutsideSet G U).ncard ≤ (G.edgeBoundary U).ncard := by
  classical
  let S : Set V := diestelDegreeTwoOutsideSet G U
  let f : S → G.edgeBoundary U := fun v =>
    ⟨(boundaryEdgeOfDeleteDiestelDegreeTwo (G := G) hCubic
      (U := U) (v := v.1) v.2.1 v.2.2.1 v.2.2.2).1,
      (boundaryEdgeOfDeleteDiestelDegreeTwo (G := G) hCubic
        (U := U) (v := v.1) v.2.1 v.2.2.1 v.2.2.2).2.1⟩
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    let ea := boundaryEdgeOfDeleteDiestelDegreeTwo (G := G) hCubic
      (U := U) (v := a.1) a.2.1 a.2.2.1 a.2.2.2
    let eb := boundaryEdgeOfDeleteDiestelDegreeTwo (G := G) hCubic
      (U := U) (v := b.1) b.2.1 b.2.2.1 b.2.2.2
    have heq : ea.1 = eb.1 := Subtype.ext_iff.mp hab
    have heaInc : G.Incident a.1 ea.1 := ea.2.2
    have hebInc : G.Incident b.1 ea.1 := by
      simpa [heq] using eb.2.2
    rcases ea.2.1 with ⟨_heG, x, y, hxy, hxU, _hyG, hyU⟩
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

lemma deleteVerts_vertexSet_eq_diestelDegreeTwoOutside_union_branch
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) :
    (G.deleteVerts U).vertexSet =
      diestelDegreeTwoOutsideSet G U ∪ diestelBranchVertexSet G U := by
  ext v
  constructor
  · intro hv
    rw [Graph.vertexSet_deleteVerts] at hv
    have hge : 2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v :=
      hterminal v hv.1 hv.2
    have hle : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 3 :=
      deleteVerts_diestelDegree_le_three_of_cubic (G := G) hCubic hv.1
    have hdeg : diestelDegree (G.deleteVerts U : MultiGraph V E) v = 2 ∨
        diestelDegree (G.deleteVerts U : MultiGraph V E) v = 3 := by omega
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

lemma diestelDegreeTwoOutside_disjoint_branch {G : MultiGraph V E}
    [Finite E] (U : Set V) :
    Disjoint (diestelDegreeTwoOutsideSet G U) (diestelBranchVertexSet G U) := by
  rw [Set.disjoint_left]
  intro v hv2 hv3
  rcases hv2 with ⟨_hvG2, _hvU2, hdeg2⟩
  rcases hv3 with ⟨_hvG3, _hvU3, hdeg3⟩
  omega

lemma diestelBranchVertexSet_ncard_ge_sub_two_cycle
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsDiestelCubic)
    (C : G.DiestelCycleIn) {U : Set V} (hUV : U ⊆ G.vertexSet)
    (hscore : U.ncard + (G.edgeBoundary U).ncard ≤
      C.support.ncard + (G.edgeBoundary C.support).ncard)
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) :
    G.vertexSet.ncard - 2 * C.support.ncard ≤
      (diestelBranchVertexSet G U).ncard := by
  classical
  let D₂ : Set V := diestelDegreeTwoOutsideSet G U
  let B₃ : Set V := diestelBranchVertexSet G U
  have hR_eq :
      (G.deleteVerts U).vertexSet = D₂ ∪ B₃ := by
    simpa [D₂, B₃] using
      deleteVerts_vertexSet_eq_diestelDegreeTwoOutside_union_branch
        (G := G) hCubic (U := U) hterminal
  have hdisj : Disjoint D₂ B₃ := by
    simpa [D₂, B₃] using diestelDegreeTwoOutside_disjoint_branch (G := G) U
  have hRcard :
      (G.deleteVerts U).vertexSet.ncard = D₂.ncard + B₃.ncard := by
    rw [hR_eq, Set.ncard_union_eq hdisj]
  have hD₂le : D₂.ncard ≤ (G.edgeBoundary U).ncard := by
    simpa [D₂] using
      diestelDegreeTwoOutside_ncard_le_edgeBoundary_ncard (G := G) hCubic U
  have hboundaryC : (G.edgeBoundary C.support).ncard ≤ C.support.ncard :=
    diestel_edgeBoundary_ncard_le_cycle_support_ncard (G := G) hCubic C
  have hUD₂le : U.ncard + D₂.ncard ≤ 2 * C.support.ncard := by
    omega
  have hdel :
      (G.deleteVerts U).vertexSet.ncard = G.vertexSet.ncard - U.ncard :=
    deleteVerts_vertexSet_ncard_eq_sub (G := G) U hUV
  change G.vertexSet.ncard - 2 * C.support.ncard ≤ B₃.ncard
  omega

private lemma loop_cycle_connected {G : MultiGraph V E}
    {e : E} {v : V} (he : G.IsLoopAt e v) :
    ((G.edgeSubgraph ({e} : Set E)).induce ({v} : Set V)).Connected := by
  refine ⟨?_⟩
  intro a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  simp only [Set.mem_singleton_iff] at ha hb
  subst a
  subst b
  exact SimpleGraph.Reachable.rfl

/-- A loop is a cycle of length one in Diestel's multigraph sense. -/
def cycleOfLoop {G : MultiGraph V E} {e : E} {v : V}
    (he : G.IsLoopAt e v) : G.DiestelCycleIn where
  support := ({v} : Set V)
  edgeSupport := ({e} : Set E)
  edgeSupport_finite := by simp
  edges_inside := by
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    exact ⟨he.edge_mem, by
      intro x hx
      have hvx : v = x := he.eq_of_inc hx
      simp [hvx]⟩
  support_nonempty := ⟨v, by simp⟩
  connected := loop_cycle_connected (G := G) he
  degree_two := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp [diestelDegreeInEdgeSet, he.inc, he]

@[simp]
lemma cycleOfLoop_support {G : MultiGraph V E} {e : E} {v : V}
    (he : G.IsLoopAt e v) :
    (cycleOfLoop (G := G) he).support = ({v} : Set V) := rfl

lemma cycleOfLoop_support_ncard {G : MultiGraph V E} {e : E} {v : V}
    (he : G.IsLoopAt e v) :
    (cycleOfLoop (G := G) he).support.ncard = 1 := by
  simp

lemma hasOneDisjointDiestelCycle_of_loop {G : MultiGraph V E}
    {e : E} {v : V} (he : G.IsLoopAt e v) :
    G.HasKDisjointDiestelCycles 1 := by
  classical
  refine ⟨fun _ : Fin 1 => cycleOfLoop (G := G) he, ?_⟩
  intro i j hij
  fin_cases i
  fin_cases j
  exact (hij rfl).elim

/--
The short-cycle step in Diestel's loop-aware multigraph convention.  If a loop
exists it is already a cycle of order one; otherwise the existing loopless
short-cycle theorem applies and the resulting cycle is reinterpreted with
Diestel degree.
-/
theorem exists_diestelCycle_support_ncard_lt_log_bound {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E]
    (hNonempty : G.vertexSet.Nonempty) :
    G.IsDiestelCubic →
      (2 : ℝ) < 2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) →
        ∃ C : G.DiestelCycleIn,
          (C.support.ncard : ℝ) <
            2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) := by
  classical
  intro hCubic htwo_lt
  by_cases hloop : ∃ e : E, ∃ v : V, G.IsLoopAt e v
  · obtain ⟨e, v, he⟩ := hloop
    refine ⟨cycleOfLoop (G := G) he, ?_⟩
    rw [cycleOfLoop_support_ncard (G := G) he]
    norm_num
    nlinarith
  · have hloopless : G.Loopless := loopless_of_no_loop (G := G) hloop
    have hOldCubic : G.IsCubic :=
      isCubic_of_isDiestelCubic_of_loopless (G := G) hloopless hCubic
    obtain ⟨C, hCshort⟩ :=
      exists_cycle_support_ncard_lt_log_bound (G := G) hNonempty hOldCubic htwo_lt
    exact ⟨DiestelCycleIn.ofCycleIn_of_loopless (G := G) hloopless C, hCshort⟩

theorem exists_diestelCycle_support_ncard_lt_log_bound_of_erdosPosaS_lt
    {V : Type u} {E : Type v} (G : MultiGraph V E) [Finite V] [Finite E]
    {k : ℕ} (hk : 2 ≤ k) :
    G.IsDiestelCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        ∃ C : G.DiestelCycleIn,
          (C.support.ncard : ℝ) <
            2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) := by
  intro hCubic hLarge
  have hsix_s : (6 : ℝ) < erdosPosaS k := six_lt_erdosPosaS hk
  have hsix_n : (6 : ℝ) < (G.vertexSet.ncard : ℝ) := hsix_s.trans hLarge
  have hNonempty : G.vertexSet.Nonempty :=
    vertexSet_nonempty_of_six_lt_ncard (G := G) hsix_n
  have htwo_lt :
      (2 : ℝ) < 2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) :=
    two_lt_two_log_div_log_two_of_six_lt hsix_n
  exact exists_diestelCycle_support_ncard_lt_log_bound G hNonempty hCubic htwo_lt

theorem exists_diestelCycle_support_ncard_lt_log_bound_of_erdosPosaS_le
    {V : Type u} {E : Type v} (G : MultiGraph V E) [Finite V] [Finite E]
    {k : ℕ} (hk : 2 ≤ k) :
    G.IsDiestelCubic →
      erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
        ∃ C : G.DiestelCycleIn,
          (C.support.ncard : ℝ) <
            2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) := by
  intro hCubic hLarge
  have hsix_s : (6 : ℝ) < erdosPosaS k := six_lt_erdosPosaS hk
  have hsix_n : (6 : ℝ) < (G.vertexSet.ncard : ℝ) := hsix_s.trans_le hLarge
  have hNonempty : G.vertexSet.Nonempty :=
    vertexSet_nonempty_of_six_lt_ncard (G := G) hsix_n
  have htwo_lt :
      (2 : ℝ) < 2 * (Real.log (G.vertexSet.ncard : ℝ) / Real.log 2) :=
    two_lt_two_log_div_log_two_of_six_lt hsix_n
  exact exists_diestelCycle_support_ncard_lt_log_bound G hNonempty hCubic htwo_lt

def diestelCycleIn_of_subgraph {H G : MultiGraph V E} (hHG : H ≤ G)
    (C : H.DiestelCycleIn) : G.DiestelCycleIn where
  support := C.support
  edgeSupport := C.edgeSupport
  edgeSupport_finite := C.edgeSupport_finite
  edges_inside := by
    intro e heC
    have heInside := C.edges_inside heC
    refine ⟨hHG.edgeSet_mono heInside.1, ?_⟩
    intro v hv
    exact heInside.2 v ((inc_iff_of_subgraph_edge hHG heInside.1).mpr hv)
  support_nonempty := C.support_nonempty
  connected := by
    rcases C.connected with ⟨hpre⟩
    refine ⟨?_⟩
    intro a b
    exact (hpre a b).mono fun x y hxy => by
      rcases hxy with ⟨hne, e, heC, heH, hlinkH⟩
      exact ⟨hne, e, heC, hHG.edgeSet_mono heH, hlinkH.mono hHG⟩
  degree_two := by
    intro v hv
    let φInc :
        {e : C.edgeSupport // G.Inc e.1 v} ≃
          {e : C.edgeSupport // H.Inc e.1 v} := by
      refine
        { toFun := fun e =>
            ⟨e.1, (inc_iff_of_subgraph_edge hHG ((C.edges_inside e.1.2).1)).mpr e.2⟩
          invFun := fun e =>
            ⟨e.1, (inc_iff_of_subgraph_edge hHG ((C.edges_inside e.1.2).1)).mp e.2⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro e
        rfl
      · intro e
        rfl
    let φLoop :
        {e : C.edgeSupport // G.IsLoopAt e.1 v} ≃
          {e : C.edgeSupport // H.IsLoopAt e.1 v} := by
      refine
        { toFun := fun e =>
            ⟨e.1, (hHG.isLoopAt_congr ((C.edges_inside e.1.2).1)).mpr e.2⟩
          invFun := fun e =>
            ⟨e.1, (hHG.isLoopAt_congr ((C.edges_inside e.1.2).1)).mp e.2⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro e
        rfl
      · intro e
        rfl
    change
      Nat.card {e : C.edgeSupport // G.Inc e.1 v} +
          Nat.card {e : C.edgeSupport // G.IsLoopAt e.1 v} = 2
    rw [Nat.card_congr φInc, Nat.card_congr φLoop]
    exact C.degree_two v hv

lemma hasKDisjointDiestelCycles_of_subgraph {H G : MultiGraph V E}
    {k : ℕ} (hHG : H ≤ G) :
    H.HasKDisjointDiestelCycles k → G.HasKDisjointDiestelCycles k := by
  rintro ⟨C, hdisj⟩
  exact ⟨fun i => diestelCycleIn_of_subgraph hHG (C i), hdisj⟩

lemma disjoint_diestelCycle_of_deleteVerts {G : MultiGraph V E}
    (C : G.DiestelCycleIn) (D : DiestelCycleIn (G.deleteVerts C.support)) :
    Disjoint C.support
      (diestelCycleIn_of_subgraph (Graph.deleteVerts_le (G := G)
        (X := C.support)) D).support := by
  rw [Set.disjoint_left]
  intro v hvC hvD
  have hvDelete :
      v ∈ (G.deleteVerts C.support).vertexSet :=
    diestelCycle_support_subset_vertexSet (G := G.deleteVerts C.support) D hvD
  simpa using hvDelete.2 hvC

lemma hasKDisjointDiestelCycles_succ_of_deleteVerts {G : MultiGraph V E}
    {k : ℕ} (C : G.DiestelCycleIn) :
    HasKDisjointDiestelCycles (G.deleteVerts C.support) k →
      G.HasKDisjointDiestelCycles (k + 1) := by
  intro hpack
  rcases hpack with ⟨D, hDdisj⟩
  let liftD (i : Fin k) : G.DiestelCycleIn :=
    diestelCycleIn_of_subgraph
      (Graph.deleteVerts_le (G := G) (X := C.support)) (D i)
  refine ⟨Fin.cases C liftD, ?_⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact (hij rfl).elim
      | succ j =>
          simpa [liftD] using disjoint_diestelCycle_of_deleteVerts (G := G) C (D j)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hdisj := disjoint_diestelCycle_of_deleteVerts (G := G) C (D i)
          simpa [liftD, disjoint_comm] using hdisj
      | succ j =>
          have hij' : i ≠ j := by
            intro h
            exact hij (by simp [h])
          exact hDdisj hij'

lemma hasZeroDisjointDiestelCycles (G : MultiGraph V E) :
    G.HasKDisjointDiestelCycles 0 := by
  refine ⟨fun i : Fin 0 => Fin.elim0 i, ?_⟩
  intro i _j _hij
  exact Fin.elim0 i

theorem lemma_2_3_1_diestel_k_zero {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] :
    G.IsDiestelCubic →
      erdosPosaS 0 < (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointDiestelCycles 0 := by
  intro _hCubic _hLarge
  exact hasZeroDisjointDiestelCycles G

theorem lemma_2_3_1_diestel_k_one {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] :
    G.IsDiestelCubic →
      erdosPosaS 1 < (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointDiestelCycles 1 := by
  classical
  intro hCubic hLarge
  by_cases hloop : ∃ e : E, ∃ v : V, G.IsLoopAt e v
  · obtain ⟨e, v, he⟩ := hloop
    exact hasOneDisjointDiestelCycle_of_loop (G := G) he
  · have hloopless : G.Loopless := loopless_of_no_loop (G := G) hloop
    have hOldCubic : G.IsCubic :=
      isCubic_of_isDiestelCubic_of_loopless (G := G) hloopless hCubic
    exact hasKDisjointDiestelCycles_of_hasKDisjointCycles_of_loopless
      (G := G) hloopless (lemma_2_3_1_k_one G hOldCubic hLarge)

theorem lemma_2_3_1_diestel_k_zero_ge {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] :
    G.IsDiestelCubic →
      erdosPosaS 0 ≤ (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointDiestelCycles 0 := by
  intro _hCubic _hLarge
  exact hasZeroDisjointDiestelCycles G

theorem lemma_2_3_1_diestel_k_one_ge {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] :
    G.IsDiestelCubic →
      erdosPosaS 1 ≤ (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointDiestelCycles 1 := by
  classical
  intro hCubic hLarge
  by_cases hloop : ∃ e : E, ∃ v : V, G.IsLoopAt e v
  · obtain ⟨e, v, he⟩ := hloop
    exact hasOneDisjointDiestelCycle_of_loop (G := G) he
  · have hloopless : G.Loopless := loopless_of_no_loop (G := G) hloop
    have hOldCubic : G.IsCubic :=
      isCubic_of_isDiestelCubic_of_loopless (G := G) hloopless hCubic
    exact hasKDisjointDiestelCycles_of_hasKDisjointCycles_of_loopless
      (G := G) hloopless (lemma_2_3_1_k_one_ge G hOldCubic hLarge)

theorem lemma_2_3_1_diestel_small_k {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ) :
    k ≤ 1 →
      G.IsDiestelCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointDiestelCycles k := by
  intro hk hCubic hLarge
  interval_cases k
  · exact lemma_2_3_1_diestel_k_zero G hCubic hLarge
  · exact lemma_2_3_1_diestel_k_one G hCubic hLarge

theorem lemma_2_3_1_diestel_small_k_ge {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ) :
    k ≤ 1 →
      G.IsDiestelCubic →
        erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointDiestelCycles k := by
  intro hk hCubic hLarge
  interval_cases k
  · exact lemma_2_3_1_diestel_k_zero_ge G hCubic hLarge
  · exact lemma_2_3_1_diestel_k_one_ge G hCubic hLarge

def DiestelCyclePackingTransfer {V' : Type u} {E' : Type v}
    (H : MultiGraph V' E') (G : MultiGraph V E) : Prop :=
  ∀ k : ℕ, H.HasKDisjointDiestelCycles k → G.HasKDisjointDiestelCycles k

lemma diestelCyclePackingTransfer_deleteVerts_of_subset {G : MultiGraph V E}
    {X Y : Set V} (hXY : X ⊆ Y) :
    DiestelCyclePackingTransfer (G.deleteVerts Y) (G.deleteVerts X) := by
  intro k hpack
  exact hasKDisjointDiestelCycles_of_subgraph (deleteVerts_anti (G := G) hXY) hpack

def HasDiestelSuppressedCubicKernel (G : MultiGraph V E) [Finite V] [Finite E]
    (U : Set V) : Prop :=
  ∃ V' : Type u, ∃ E' : Type v,
    ∃ hfinV' : Finite V', ∃ hfinE' : Finite E',
    ∃ H : MultiGraph V' E',
      @IsDiestelCubic V' E' H hfinE' ∧
        (diestelBranchVertexSet G U).ncard ≤ H.vertexSet.ncard ∧
          DiestelCyclePackingTransfer H (G.deleteVerts U)

lemma deleteVerts_isDiestelCubic_of_all_outside_diestelDegree_three
    {G : MultiGraph V E} [Finite E] (U : Set V)
    (hdeg3 : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      diestelDegree (G.deleteVerts U : MultiGraph V E) v = 3) :
    IsDiestelCubic (G.deleteVerts U : MultiGraph V E) := by
  intro v hv
  rw [Graph.vertexSet_deleteVerts] at hv
  exact hdeg3 v hv.1 hv.2

lemma diestelBranchVertexSet_subset_deleteVerts_vertexSet
    {G : MultiGraph V E} [Finite E] (U : Set V) :
    diestelBranchVertexSet G U ⊆ (G.deleteVerts U).vertexSet := by
  intro v hv
  rw [Graph.vertexSet_deleteVerts]
  exact ⟨hv.1, hv.2.1⟩

lemma hasDiestelSuppressedCubicKernel_of_all_outside_diestelDegree_three
    {G : MultiGraph V E} [Finite V] [Finite E] (U : Set V)
    (hdeg3 : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      diestelDegree (G.deleteVerts U : MultiGraph V E) v = 3) :
    HasDiestelSuppressedCubicKernel G U := by
  refine ⟨V, E, inferInstance, inferInstance, G.deleteVerts U, ?_, ?_, ?_⟩
  · exact deleteVerts_isDiestelCubic_of_all_outside_diestelDegree_three
      (G := G) U hdeg3
  · exact Set.ncard_le_ncard
      (diestelBranchVertexSet_subset_deleteVerts_vertexSet (G := G) U)
  · intro k hpack
    exact hpack

lemma all_outside_diestelDegree_three_of_terminal_degreeTwoOutside_eq_empty
    {G : MultiGraph V E} [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v)
    (hD₂ : diestelDegreeTwoOutsideSet G U = ∅) :
    ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      diestelDegree (G.deleteVerts U : MultiGraph V E) v = 3 := by
  intro v hvG hvU
  have hge : 2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v :=
    hterminal v hvG hvU
  have hle : diestelDegree (G.deleteVerts U : MultiGraph V E) v ≤ 3 :=
    deleteVerts_diestelDegree_le_three_of_cubic (G := G) hCubic hvG
  have hdeg :
      diestelDegree (G.deleteVerts U : MultiGraph V E) v = 2 ∨
        diestelDegree (G.deleteVerts U : MultiGraph V E) v = 3 := by
    omega
  rcases hdeg with hdeg | hdeg
  · have hvD : v ∈ diestelDegreeTwoOutsideSet G U := ⟨hvG, hvU, hdeg⟩
    rw [hD₂] at hvD
    simp at hvD
  · exact hdeg

lemma hasDiestelSuppressedCubicKernel_of_terminal_degreeTwoOutside_eq_empty
    {G : MultiGraph V E} [Finite V] [Finite E] (hCubic : G.IsDiestelCubic)
    {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v)
    (hD₂ : diestelDegreeTwoOutsideSet G U = ∅) :
    HasDiestelSuppressedCubicKernel G U :=
  hasDiestelSuppressedCubicKernel_of_all_outside_diestelDegree_three
    (G := G) U
    (all_outside_diestelDegree_three_of_terminal_degreeTwoOutside_eq_empty
      (G := G) hCubic hterminal hD₂)

def HasDiestelCyclePackingReduction (G : MultiGraph V E) [Finite V] [Finite E]
    (k : ℕ) : Prop :=
  ∃ C : G.DiestelCycleIn, ∃ V' : Type u, ∃ E' : Type v,
    ∃ hfinV' : Finite V', ∃ hfinE' : Finite E',
    ∃ H : MultiGraph V' E',
      @IsDiestelCubic V' E' H hfinE' ∧
        erdosPosaS (k - 1) < (H.vertexSet.ncard : ℝ) ∧
          DiestelCyclePackingTransfer H (G.deleteVerts C.support)

theorem hasDiestelCyclePackingReduction_of_suppressed_kernel
    {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (hk : 2 ≤ k)
    (hAnalytic :
      erdosPosaS (k - 1) < erdosPosaS k - 4 * logTwo (erdosPosaS k))
    (hKernel : ∀ C : G.DiestelCycleIn, ∀ U : Set V,
      C.support ⊆ U →
        U ⊆ G.vertexSet →
          U.ncard + (G.edgeBoundary U).ncard ≤
            C.support.ncard + (G.edgeBoundary C.support).ncard →
            (∀ v : V, v ∈ G.vertexSet → v ∉ U →
              2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) →
              HasDiestelSuppressedCubicKernel G U) :
    G.IsDiestelCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        HasDiestelCyclePackingReduction G k := by
  classical
  intro hCubic hLarge
  obtain ⟨C, hCshort⟩ :=
    exists_diestelCycle_support_ncard_lt_log_bound_of_erdosPosaS_lt
      (G := G) hk hCubic hLarge
  obtain ⟨U, hCU, hUV, hscore, hterminal⟩ :=
    exists_pruned_superset_of_diestelCycle_support_with_score
      (G := G) hCubic C
  obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranchH, htransferU⟩ :=
    hKernel C U hCU hUV hscore hterminal
  haveI : Finite V' := hfinV'
  haveI : Finite E' := hfinE'
  have hsix : (6 : ℝ) ≤ erdosPosaS k :=
    (six_lt_erdosPosaS hk).le
  have hmono :
      erdosPosaS k - 4 * logTwo (erdosPosaS k) ≤
        (G.vertexSet.ncard : ℝ) - 4 * logTwo (G.vertexSet.ncard : ℝ) :=
    sub_four_logTwo_mono_on_six hsix hLarge.le
  have hbefore_log :
      erdosPosaS (k - 1) <
        (G.vertexSet.ncard : ℝ) - 4 * logTwo (G.vertexSet.ncard : ℝ) :=
    hAnalytic.trans_le hmono
  have hCshort' :
      (C.support.ncard : ℝ) <
        2 * logTwo (G.vertexSet.ncard : ℝ) := by
    simpa [logTwo] using hCshort
  have hbefore_cycle :
      erdosPosaS (k - 1) <
        (G.vertexSet.ncard : ℝ) - 2 * (C.support.ncard : ℝ) := by
    nlinarith
  have htwoc_lt_n :
      2 * C.support.ncard < G.vertexSet.ncard := by
    have hs_nonneg : 0 ≤ erdosPosaS (k - 1) := erdosPosaS_nonneg (k - 1)
    by_contra hnot
    have hnle : G.vertexSet.ncard ≤ 2 * C.support.ncard := Nat.le_of_not_gt hnot
    have hnle_real :
        (G.vertexSet.ncard : ℝ) ≤ 2 * (C.support.ncard : ℝ) := by
      exact_mod_cast hnle
    nlinarith
  have htwoc_le_n : 2 * C.support.ncard ≤ G.vertexSet.ncard :=
    htwoc_lt_n.le
  have hbranchLowerNat :
      G.vertexSet.ncard - 2 * C.support.ncard ≤
        (diestelBranchVertexSet G U).ncard :=
    diestelBranchVertexSet_ncard_ge_sub_two_cycle
      (G := G) hCubic C hUV hscore hterminal
  have hbranchLowerReal :
      ((G.vertexSet.ncard - 2 * C.support.ncard : ℕ) : ℝ) ≤
        ((diestelBranchVertexSet G U).ncard : ℝ) := by
    exact_mod_cast hbranchLowerNat
  have hsub_cast :
      ((G.vertexSet.ncard - 2 * C.support.ncard : ℕ) : ℝ) =
        (G.vertexSet.ncard : ℝ) - 2 * (C.support.ncard : ℝ) := by
    rw [Nat.cast_sub htwoc_le_n]
    norm_num
  have hbranchLarge :
      erdosPosaS (k - 1) < ((diestelBranchVertexSet G U).ncard : ℝ) := by
    rw [hsub_cast] at hbranchLowerReal
    exact hbefore_cycle.trans_le hbranchLowerReal
  have hHLarge : erdosPosaS (k - 1) < (H.vertexSet.ncard : ℝ) := by
    have hbranchHReal :
        ((diestelBranchVertexSet G U).ncard : ℝ) ≤ (H.vertexSet.ncard : ℝ) := by
      exact_mod_cast hbranchH
    exact hbranchLarge.trans_le hbranchHReal
  let htransferDelete :
      DiestelCyclePackingTransfer (G.deleteVerts U) (G.deleteVerts C.support) :=
    diestelCyclePackingTransfer_deleteVerts_of_subset (G := G) hCU
  refine ⟨C, V', E', hfinV', hfinE', H, hHCubic, hHLarge, ?_⟩
  intro l hpack
  exact htransferDelete l (htransferU l hpack)

theorem hasDiestelCyclePackingReduction_of_suppressed_kernel_ge
    {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (hk : 2 ≤ k)
    (hAnalytic :
      erdosPosaS (k - 1) < erdosPosaS k - 4 * logTwo (erdosPosaS k))
    (hKernel : ∀ C : G.DiestelCycleIn, ∀ U : Set V,
      C.support ⊆ U →
        U ⊆ G.vertexSet →
          U.ncard + (G.edgeBoundary U).ncard ≤
            C.support.ncard + (G.edgeBoundary C.support).ncard →
            (∀ v : V, v ∈ G.vertexSet → v ∉ U →
              2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) →
              HasDiestelSuppressedCubicKernel G U) :
    G.IsDiestelCubic →
      erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
        HasDiestelCyclePackingReduction G k := by
  classical
  intro hCubic hLarge
  obtain ⟨C, hCshort⟩ :=
    exists_diestelCycle_support_ncard_lt_log_bound_of_erdosPosaS_le
      (G := G) hk hCubic hLarge
  obtain ⟨U, hCU, hUV, hscore, hterminal⟩ :=
    exists_pruned_superset_of_diestelCycle_support_with_score
      (G := G) hCubic C
  obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranchH, htransferU⟩ :=
    hKernel C U hCU hUV hscore hterminal
  haveI : Finite V' := hfinV'
  haveI : Finite E' := hfinE'
  have hsix : (6 : ℝ) ≤ erdosPosaS k :=
    (six_lt_erdosPosaS hk).le
  have hmono :
      erdosPosaS k - 4 * logTwo (erdosPosaS k) ≤
        (G.vertexSet.ncard : ℝ) - 4 * logTwo (G.vertexSet.ncard : ℝ) :=
    sub_four_logTwo_mono_on_six hsix hLarge
  have hbefore_log :
      erdosPosaS (k - 1) <
        (G.vertexSet.ncard : ℝ) - 4 * logTwo (G.vertexSet.ncard : ℝ) :=
    hAnalytic.trans_le hmono
  have hCshort' :
      (C.support.ncard : ℝ) <
        2 * logTwo (G.vertexSet.ncard : ℝ) := by
    simpa [logTwo] using hCshort
  have hbefore_cycle :
      erdosPosaS (k - 1) <
        (G.vertexSet.ncard : ℝ) - 2 * (C.support.ncard : ℝ) := by
    nlinarith
  have htwoc_lt_n :
      2 * C.support.ncard < G.vertexSet.ncard := by
    have hs_nonneg : 0 ≤ erdosPosaS (k - 1) := erdosPosaS_nonneg (k - 1)
    by_contra hnot
    have hnle : G.vertexSet.ncard ≤ 2 * C.support.ncard := Nat.le_of_not_gt hnot
    have hnle_real :
        (G.vertexSet.ncard : ℝ) ≤ 2 * (C.support.ncard : ℝ) := by
      exact_mod_cast hnle
    nlinarith
  have htwoc_le_n : 2 * C.support.ncard ≤ G.vertexSet.ncard :=
    htwoc_lt_n.le
  have hbranchLowerNat :
      G.vertexSet.ncard - 2 * C.support.ncard ≤
        (diestelBranchVertexSet G U).ncard :=
    diestelBranchVertexSet_ncard_ge_sub_two_cycle
      (G := G) hCubic C hUV hscore hterminal
  have hbranchLowerReal :
      ((G.vertexSet.ncard - 2 * C.support.ncard : ℕ) : ℝ) ≤
        ((diestelBranchVertexSet G U).ncard : ℝ) := by
    exact_mod_cast hbranchLowerNat
  have hsub_cast :
      ((G.vertexSet.ncard - 2 * C.support.ncard : ℕ) : ℝ) =
        (G.vertexSet.ncard : ℝ) - 2 * (C.support.ncard : ℝ) := by
    rw [Nat.cast_sub htwoc_le_n]
    norm_num
  have hbranchLarge :
      erdosPosaS (k - 1) < ((diestelBranchVertexSet G U).ncard : ℝ) := by
    rw [hsub_cast] at hbranchLowerReal
    exact hbefore_cycle.trans_le hbranchLowerReal
  have hHLarge : erdosPosaS (k - 1) < (H.vertexSet.ncard : ℝ) := by
    have hbranchHReal :
        ((diestelBranchVertexSet G U).ncard : ℝ) ≤ (H.vertexSet.ncard : ℝ) := by
      exact_mod_cast hbranchH
    exact hbranchLarge.trans_le hbranchHReal
  let htransferDelete :
      DiestelCyclePackingTransfer (G.deleteVerts U) (G.deleteVerts C.support) :=
    diestelCyclePackingTransfer_deleteVerts_of_subset (G := G) hCU
  refine ⟨C, V', E', hfinV', hfinE', H, hHCubic, hHLarge, ?_⟩
  intro l hpack
  exact htransferDelete l (htransferU l hpack)

theorem hasDiestelCyclePackingReduction_of_suppressed_kernel'
    {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (hk : 2 ≤ k)
    (hKernel : ∀ C : G.DiestelCycleIn, ∀ U : Set V,
      C.support ⊆ U →
        U ⊆ G.vertexSet →
          U.ncard + (G.edgeBoundary U).ncard ≤
            C.support.ncard + (G.edgeBoundary C.support).ncard →
            (∀ v : V, v ∈ G.vertexSet → v ∉ U →
              2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) →
              HasDiestelSuppressedCubicKernel G U) :
    G.IsDiestelCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        HasDiestelCyclePackingReduction G k :=
  hasDiestelCyclePackingReduction_of_suppressed_kernel (G := G) hk
    (erdosPosaS_pred_lt_sub_four_logTwo hk) hKernel

theorem hasDiestelCyclePackingReduction_of_suppressed_kernel_ge'
    {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (hk : 2 ≤ k)
    (hKernel : ∀ C : G.DiestelCycleIn, ∀ U : Set V,
      C.support ⊆ U →
        U ⊆ G.vertexSet →
          U.ncard + (G.edgeBoundary U).ncard ≤
            C.support.ncard + (G.edgeBoundary C.support).ncard →
            (∀ v : V, v ∈ G.vertexSet → v ∉ U →
              2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) →
              HasDiestelSuppressedCubicKernel G U) :
    G.IsDiestelCubic →
      erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
        HasDiestelCyclePackingReduction G k :=
  hasDiestelCyclePackingReduction_of_suppressed_kernel_ge (G := G) hk
    (erdosPosaS_pred_lt_sub_four_logTwo hk) hKernel


private theorem lemma_2_3_1_diestel_from_reduction_aux :
    ∀ k : ℕ,
      (∀ l < k, ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
        [Finite V] [Finite E],
          G.IsDiestelCubic →
            erdosPosaS l < (G.vertexSet.ncard : ℝ) →
              G.HasKDisjointDiestelCycles l) →
        ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
          [Finite V] [Finite E],
          (2 ≤ k → G.IsDiestelCubic →
            erdosPosaS k < (G.vertexSet.ncard : ℝ) →
              HasDiestelCyclePackingReduction G k) →
            G.IsDiestelCubic →
              erdosPosaS k < (G.vertexSet.ncard : ℝ) →
                G.HasKDisjointDiestelCycles k := by
  intro k ih V E G _ _ hreduce hCubic hLarge
  by_cases hsmall : k ≤ 1
  · exact lemma_2_3_1_diestel_small_k G k hsmall hCubic hLarge
  · have hk : 2 ≤ k := by omega
    obtain ⟨C, V', E', hfinV', hfinE', H, hHCubic, hHLarge, htransfer⟩ :=
      hreduce hk hCubic hLarge
    haveI : Finite V' := hfinV'
    haveI : Finite E' := hfinE'
    have hkpred_lt : k - 1 < k := by omega
    have hHpack : H.HasKDisjointDiestelCycles (k - 1) :=
      ih (k - 1) hkpred_lt H hHCubic hHLarge
    have hDeletePack : HasKDisjointDiestelCycles (G.deleteVerts C.support) (k - 1) :=
      htransfer (k - 1) hHpack
    have hSuccPack : G.HasKDisjointDiestelCycles ((k - 1) + 1) :=
      hasKDisjointDiestelCycles_succ_of_deleteVerts (G := G) C hDeletePack
    have hk_eq : (k - 1) + 1 = k := by omega
    simpa [hk_eq] using hSuccPack

theorem lemma_2_3_1_diestel_from_reductions
    (hreduce : ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
        2 ≤ k →
          G.IsDiestelCubic →
            erdosPosaS k < (G.vertexSet.ncard : ℝ) →
              HasDiestelCyclePackingReduction G k) :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
      G.IsDiestelCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointDiestelCycles k := by
  intro V E G _ _ k
  exact Nat.strong_induction_on k
    (p := fun k => ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E],
      G.IsDiestelCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointDiestelCycles k)
    (fun k ih => by
    intro V E G _ _ hCubic hLarge
    exact lemma_2_3_1_diestel_from_reduction_aux k ih G
      (fun hk => hreduce G k hk) hCubic hLarge) G

theorem lemma_2_3_1_diestel_from_reductions_ge
    (hreduce : ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
        2 ≤ k →
          G.IsDiestelCubic →
            erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
              HasDiestelCyclePackingReduction G k) :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
      G.IsDiestelCubic →
        erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointDiestelCycles k := by
  intro V E G _ _ k hCubic hLarge
  have hstrict :
      ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
        [Finite V] [Finite E] (k : ℕ),
        G.IsDiestelCubic →
          erdosPosaS k < (G.vertexSet.ncard : ℝ) →
            G.HasKDisjointDiestelCycles k :=
    lemma_2_3_1_diestel_from_reductions
      (fun G _hfinV _hfinE k hk hCubic hLarge =>
        hreduce G k hk hCubic hLarge.le)
  by_cases hsmall : k ≤ 1
  · exact lemma_2_3_1_diestel_small_k_ge G k hsmall hCubic hLarge
  · have hk : 2 ≤ k := by omega
    obtain ⟨C, V', E', hfinV', hfinE', H, hHCubic, hHLarge, htransfer⟩ :=
      hreduce G k hk hCubic hLarge
    haveI : Finite V' := hfinV'
    haveI : Finite E' := hfinE'
    have hHpack : H.HasKDisjointDiestelCycles (k - 1) :=
      hstrict H (k - 1) hHCubic hHLarge
    have hDeletePack : HasKDisjointDiestelCycles (G.deleteVerts C.support) (k - 1) :=
      htransfer (k - 1) hHpack
    have hSuccPack : G.HasKDisjointDiestelCycles ((k - 1) + 1) :=
      hasKDisjointDiestelCycles_succ_of_deleteVerts (G := G) C hDeletePack
    have hk_eq : (k - 1) + 1 = k := by omega
    simpa [hk_eq] using hSuccPack

theorem lemma_2_3_1_diestel_from_suppressed_kernels
    (hKernel : ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E], ∀ C : G.DiestelCycleIn, ∀ U : Set V,
        C.support ⊆ U →
          U ⊆ G.vertexSet →
            U.ncard + (G.edgeBoundary U).ncard ≤
              C.support.ncard + (G.edgeBoundary C.support).ncard →
              (∀ v : V, v ∈ G.vertexSet → v ∉ U →
                2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) →
                HasDiestelSuppressedCubicKernel G U) :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
      G.IsDiestelCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointDiestelCycles k := by
  exact lemma_2_3_1_diestel_from_reductions
    (fun G _hfinV _hfinE k hk hCubic hLarge =>
      hasDiestelCyclePackingReduction_of_suppressed_kernel'
        (G := G) (k := k) hk (hKernel (G := G)) hCubic hLarge)

theorem lemma_2_3_1_loopless_from_diestel_reductions
    (hreduce : ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
        2 ≤ k →
          G.IsDiestelCubic →
            erdosPosaS k < (G.vertexSet.ncard : ℝ) →
              HasDiestelCyclePackingReduction G k) :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
      G.IsCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointCycles k := by
  intro V E G _ _ k hCubic hLarge
  have hDpack : G.HasKDisjointDiestelCycles k :=
    lemma_2_3_1_diestel_from_reductions hreduce G k
      (isDiestelCubic_of_isCubic (G := G) hCubic) hLarge
  exact hasKDisjointCycles_of_hasKDisjointDiestelCycles_of_loopless
    (G := G) hCubic.1 hDpack

theorem lemma_2_3_1_loopless_from_diestel_suppressed_kernels
    (hKernel : ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E], ∀ C : G.DiestelCycleIn, ∀ U : Set V,
        C.support ⊆ U →
          U ⊆ G.vertexSet →
            U.ncard + (G.edgeBoundary U).ncard ≤
              C.support.ncard + (G.edgeBoundary C.support).ncard →
              (∀ v : V, v ∈ G.vertexSet → v ∉ U →
                2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) →
                HasDiestelSuppressedCubicKernel G U) :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E)
      [Finite V] [Finite E] (k : ℕ),
      G.IsCubic →
        erdosPosaS k < (G.vertexSet.ncard : ℝ) →
          G.HasKDisjointCycles k := by
  intro V E G _ _ k hCubic hLarge
  have hDpack : G.HasKDisjointDiestelCycles k :=
    lemma_2_3_1_diestel_from_suppressed_kernels hKernel G k
      (isDiestelCubic_of_isCubic (G := G) hCubic) hLarge
  exact hasKDisjointCycles_of_hasKDisjointDiestelCycles_of_loopless
    (G := G) hCubic.1 hDpack

lemma diestelDegree_eq_two_cases {G : MultiGraph V E} [Finite E]
    {v : V} (hdeg : G.diestelDegree v = 2) :
    (∃ e : E, G.IsLoopAt e v ∧
      ∀ f : E, G.Incident v f → f = e) ∨
    (∃ e f : E, ∃ x y : V,
      e ≠ f ∧ x ≠ v ∧ y ≠ v ∧
        G.IsLink e v x ∧ G.IsLink f v y ∧
          ∀ g : E, G.Incident v g → g = e ∨ g = f) := by
  classical
  let I : Set E := {e : E | G.Incident v e}
  let L : Set E := G.loopSetAt v
  have hLI : L ⊆ I := by
    simpa [I, L] using loopSetAt_subset_incident (G := G) v
  have hLIcard : L.ncard ≤ I.ncard := Set.ncard_le_ncard hLI
  have hsum : I.ncard + L.ncard = 2 := by
    simpa [I, L, diestelDegree] using hdeg
  have hcases : (L.ncard = 0 ∧ I.ncard = 2) ∨
      (L.ncard = 1 ∧ I.ncard = 1) := by
    omega
  rcases hcases with hnoLoop | hLoop
  · right
    have hLempty : L = ∅ := by
      exact (Set.ncard_eq_zero (s := L)).mp hnoLoop.1
    obtain ⟨e, f, hef, hIpair⟩ := Set.ncard_eq_two.mp hnoLoop.2
    have heI : e ∈ I := by rw [hIpair]; simp
    have hfI : f ∈ I := by rw [hIpair]; simp [hef.symm]
    rcases heI with ⟨heEdge, heInc⟩
    rcases hfI with ⟨hfEdge, hfInc⟩
    rcases heInc with ⟨x, hex⟩
    rcases hfInc with ⟨y, hfy⟩
    have hxv : x ≠ v := by
      intro hx
      have heL : e ∈ L := by
        refine ⟨hex.edge_mem, ?_⟩
        subst x
        exact hex
      rw [hLempty] at heL
      simp at heL
    have hyv : y ≠ v := by
      intro hy
      have hfL : f ∈ L := by
        refine ⟨hfy.edge_mem, ?_⟩
        subst y
        exact hfy
      rw [hLempty] at hfL
      simp at hfL
    refine ⟨e, f, x, y, hef, hxv, hyv, hex, hfy, ?_⟩
    intro g hg
    have hgI : g ∈ I := hg
    rw [hIpair] at hgI
    simpa using hgI
  · left
    obtain ⟨e, hLsingleton⟩ := Set.ncard_eq_one.mp hLoop.1
    have heL : e ∈ L := by
      rw [hLsingleton]
      simp
    obtain ⟨a, hIsingleton⟩ := Set.ncard_eq_one.mp hLoop.2
    have heI : e ∈ I := hLI heL
    have hea : e = a := by
      rw [hIsingleton] at heI
      simpa using heI
    refine ⟨e, heL.2, ?_⟩
    intro f hf
    have hfI : f ∈ I := hf
    rw [hIsingleton] at hfI
    have hfa : f = a := by simpa using hfI
    exact hfa.trans hea.symm

namespace Suppression

/--
The edge labels after suppressing a degree-two vertex by replacing two
distinct old edges with one new edge.
-/
  abbrev StepEdge (E : Type v) := Sum E Unit

/--
Suppress a specified pair of distinct edges `e` and `f` incident with `v`.
The old edges other than `e` and `f` remain, with any old link through `v`
discarded by the induced vertex set.  The new edge links the other endpoints
`x` and `y`; if `x = y`, this is a loop, as in Diestel's Section 1.10.
-/
def suppressPair (G : MultiGraph V E) (v x y : V) (e f : E) :
    MultiGraph V (StepEdge E) where
  vertexSet := G.vertexSet \ {v}
  IsLink g a b :=
    match g with
    | Sum.inl old =>
        old ≠ e ∧ old ≠ f ∧ G.IsLink old a b ∧ a ≠ v ∧ b ≠ v
    | Sum.inr _ =>
        (a = x ∧ b = y ∨ a = y ∧ b = x) ∧
          x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v
  isLink_symm := by
    intro g hg a b h
    cases g with
    | inl old =>
        exact ⟨h.1, h.2.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩
    | inr u =>
        exact ⟨by
          rcases h.1 with hxy | hyx
          · exact Or.inr ⟨hxy.2, hxy.1⟩
          · exact Or.inl ⟨hyx.2, hyx.1⟩,
          h.2⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro g a b c d h₁ h₂
    cases g with
    | inl old =>
        exact h₁.2.2.1.left_eq_or_eq h₂.2.2.1
    | inr u =>
        rcases h₁.1 with h₁ | h₁ <;> rcases h₂.1 with h₂ | h₂
        · exact Or.inl (h₁.1.trans h₂.1.symm)
        · exact Or.inr (h₁.1.trans h₂.2.symm)
        · exact Or.inr (h₁.1.trans h₂.2.symm)
        · exact Or.inl (h₁.1.trans h₂.1.symm)
  left_mem_of_isLink := by
    intro g a b h
    cases g with
    | inl old =>
        exact ⟨h.2.2.1.left_mem, by simpa using h.2.2.2.1⟩
    | inr u =>
        rcases h.1 with hxy | hyx
        · exact ⟨hxy.1 ▸ h.2.1, by simpa [hxy.1] using h.2.2.2.1⟩
        · exact ⟨hyx.1 ▸ h.2.2.1, by simpa [hyx.1] using h.2.2.2.2⟩

@[simp]
lemma suppressPair_vertexSet (G : MultiGraph V E) (v x y : V) (e f : E) :
    (suppressPair G v x y e f).vertexSet = G.vertexSet \ {v} := rfl

lemma suppressPair_vertexSet_ncard {G : MultiGraph V E}
    [Finite V] {v x y : V} {e f : E} (hv : v ∈ G.vertexSet) :
    (suppressPair G v x y e f).vertexSet.ncard = G.vertexSet.ncard - 1 := by
  rw [suppressPair_vertexSet, Set.ncard_diff (by
    intro z hz
    simpa [Set.mem_singleton_iff.mp hz] using hv)]
  simp [hv]

lemma suppressPair_vertexSet_subset {G : MultiGraph V E}
    {v x y : V} {e f : E} :
    (suppressPair G v x y e f).vertexSet ⊆ G.vertexSet := by
  intro a ha
  rw [suppressPair_vertexSet] at ha
  exact ha.1

lemma suppressPair_removed_not_mem_vertexSet (G : MultiGraph V E)
    (v x y : V) (e f : E) :
    v ∉ (suppressPair G v x y e f).vertexSet := by
  rw [suppressPair_vertexSet]
  simp

lemma suppressPair_new_isLink {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (suppressPair G v x y e f).IsLink
      (Sum.inr ()) x y := by
  exact ⟨Or.inl ⟨rfl, rfl⟩, hx, hy, hxv, hyv⟩

lemma suppressPair_old_isLink {G : MultiGraph V E}
    {v x y a b : V} {e f old : E}
    (hoe : old ≠ e) (hof : old ≠ f)
    (h : G.IsLink old a b) (hav : a ≠ v) (hbv : b ≠ v) :
    (suppressPair G v x y e f).IsLink (Sum.inl old) a b :=
  ⟨hoe, hof, h, hav, hbv⟩

lemma suppressPair_old_inc_iff {G : MultiGraph V E}
    {v x y a : V} {e f old : E} :
    (suppressPair G v x y e f).Inc (Sum.inl old) a ↔
      old ≠ e ∧ old ≠ f ∧ (G.deleteVerts ({v} : Set V)).Inc old a := by
  constructor
  · rintro ⟨b, hlink⟩
    refine ⟨hlink.1, hlink.2.1, ?_⟩
    refine ⟨b, ?_⟩
    rw [Graph.deleteVerts_isLink]
    exact ⟨hlink.2.2.1, by simpa using hlink.2.2.2.1,
      by simpa using hlink.2.2.2.2⟩
  · rintro ⟨hoe, hof, hinc⟩
    rcases hinc with ⟨b, hlink⟩
    rw [Graph.deleteVerts_isLink] at hlink
    exact ⟨b, suppressPair_old_isLink
      (G := G) (v := v) (x := x) (y := y) hoe hof
      hlink.1 hlink.2.1 hlink.2.2⟩

lemma suppressPair_old_loopAt_iff {G : MultiGraph V E}
    {v x y a : V} {e f old : E} :
    (suppressPair G v x y e f).IsLoopAt (Sum.inl old) a ↔
      old ≠ e ∧ old ≠ f ∧ G.IsLoopAt old a ∧ a ≠ v := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · rintro ⟨hoe, hof, hloop, hav⟩
    exact suppressPair_old_isLink
      (G := G) (v := v) (x := x) (y := y) hoe hof hloop hav hav

lemma suppressPair_new_inc_iff {G : MultiGraph V E}
    {v x y a : V} {e f : E} :
    (suppressPair G v x y e f).Inc
      (Sum.inr ()) a ↔
      (a = x ∨ a = y) ∧
        x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v := by
  constructor
  · rintro ⟨b, hlink⟩
    refine ⟨?_, hlink.2⟩
    rcases hlink.1 with hxy | hyx
    · exact Or.inl hxy.1
    · exact Or.inr hyx.1
  · rintro ⟨ha, hx, hy, hxv, hyv⟩
    rcases ha with rfl | rfl
    · exact ⟨y, suppressPair_new_isLink (G := G)
        (v := v) (e := e) (f := f) hx hy hxv hyv⟩
    · exact ⟨x, (suppressPair_new_isLink (G := G)
        (v := v) (e := e) (f := f) hx hy hxv hyv).symm⟩

lemma suppressPair_new_loopAt_iff {G : MultiGraph V E}
    {v x y a : V} {e f : E} :
    (suppressPair G v x y e f).IsLoopAt
      (Sum.inr ()) a ↔
      a = x ∧ a = y ∧
        x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v := by
  constructor
  · intro h
    rcases h.1 with hxy | hyx
    · exact ⟨hxy.1, hxy.2, h.2⟩
    · exact ⟨hyx.2, hyx.1, h.2⟩
  · rintro ⟨hax, hay, hx, hy, hxv, hyv⟩
    subst a
    have hxy : x = y := hay
    subst y
    exact suppressPair_new_isLink (G := G)
      (v := v) (e := e) (f := f) hx hx hxv hxv

lemma suppressPair_new_inc_of_eq_left {G : MultiGraph V E}
    {v x y a : V} {e f : E}
    (ha : a = x) (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (suppressPair G v x y e f).Incident a (Sum.inr ()) := by
  subst a
  have hlink := suppressPair_new_isLink (G := G)
    (v := v) (e := e) (f := f) hx hy hxv hyv
  exact ⟨hlink.edge_mem, hlink.inc_left⟩

lemma suppressPair_new_inc_of_eq_right {G : MultiGraph V E}
    {v x y a : V} {e f : E}
    (ha : a = y) (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (suppressPair G v x y e f).Incident a (Sum.inr ()) := by
  subst a
  have hlink := suppressPair_new_isLink (G := G)
    (v := v) (e := e) (f := f) hx hy hxv hyv
  exact ⟨hlink.edge_mem, hlink.inc_right⟩

lemma suppressPair_new_loop_incident {G : MultiGraph V E}
    {v x y a : V} {e f : E}
    (hax : a = x) (hay : a = y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (Sum.inr () : StepEdge E) ∈
      (suppressPair G v x y e f).loopSetAt a := by
  have hloop :
      (suppressPair G v x y e f).IsLoopAt (Sum.inr ()) a := by
    rw [suppressPair_new_loopAt_iff]
    exact ⟨hax, hay, hx, hy, hxv, hyv⟩
  exact ⟨hloop.edge_mem, hloop⟩

private lemma suppressPair_edge_ne_of_inc_not_endpoint {G : MultiGraph V E}
    {v x y a : V} {e f g : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y)
    (hg : G.Incident a g) :
    g ≠ e ∧ g ≠ f := by
  constructor
  · intro hge
    subst g
    rcases hg.2.eq_or_eq_of_isLink he with hav' | hax'
    · exact hav hav'
    · exact hax hax'
  · intro hgf
    subst g
    rcases hg.2.eq_or_eq_of_isLink hf with hav' | hay'
    · exact hav hav'
    · exact hay hay'

private lemma suppressPair_other_endpoint_ne_v {G : MultiGraph V E}
    {v x y a b : V} {e f g : E}
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hge : g ≠ e) (hgf : g ≠ f)
    (hlink : G.IsLink g a b) :
    b ≠ v := by
  intro hbv
  have hgv : G.Incident v g := by
    exact ⟨hlink.edge_mem, by
      simpa [hbv] using hlink.inc_right⟩
  rcases hvef g hgv with rfl | rfl
  · exact hge rfl
  · exact hgf rfl

private lemma suppressPair_old_inc_of_original_inc_not_removed {G : MultiGraph V E}
    {v x y a : V} {e f g : E}
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hge : g ≠ e) (hgf : g ≠ f) (hav : a ≠ v)
    (hg : G.Incident a g) :
    (suppressPair G v x y e f).Incident a (Sum.inl g) := by
  classical
  let b : V := hg.2.other
  have hlink : G.IsLink g a b := hg.2.isLink_other
  have hbv : b ≠ v :=
    suppressPair_other_endpoint_ne_v (G := G) (v := v)
      (x := x) (y := y) (a := a) (b := b) (e := e) (f := f)
      hvef hge hgf hlink
  have hdel : (G.deleteVerts ({v} : Set V)).Inc g a := by
    refine ⟨b, ?_⟩
    rw [Graph.deleteVerts_isLink]
    exact ⟨hlink, by simpa using hav, by simpa using hbv⟩
  have hHinc : (suppressPair G v x y e f).Inc (Sum.inl g) a :=
    (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
      (a := a) (e := e) (f := f) (old := g)).mpr ⟨hge, hgf, hdel⟩
  exact ⟨hHinc.edge_mem, hHinc⟩

private lemma suppressPair_old_loop_of_original_loop_not_removed {G : MultiGraph V E}
    {v x y a : V} {e f g : E}
    (hge : g ≠ e) (hgf : g ≠ f) (hav : a ≠ v)
    (hg : g ∈ G.loopSetAt a) :
    (Sum.inl g : StepEdge E) ∈
      (suppressPair G v x y e f).loopSetAt a := by
  have hHloop : (suppressPair G v x y e f).IsLoopAt (Sum.inl g) a :=
    (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
      (a := a) (e := e) (f := f) (old := g)).mpr
      ⟨hge, hgf, hg.2, hav⟩
  exact ⟨hHloop.edge_mem, hHloop⟩

private lemma suppressPair_not_inc_left_of_right_edge {G : MultiGraph V E}
    {v x y : V} {f : E} (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hxy : x ≠ y) :
    ¬ G.Incident x f := by
  intro hinc
  rcases hinc.2.eq_or_eq_of_isLink hf with hxv' | hxy'
  · exact hxv hxv'
  · exact hxy hxy'

private lemma suppressPair_not_inc_right_of_left_edge {G : MultiGraph V E}
    {v x y : V} {e : E} (he : G.IsLink e v x)
    (hyv : y ≠ v) (hyx : y ≠ x) :
    ¬ G.Incident y e := by
  intro hinc
  rcases hinc.2.eq_or_eq_of_isLink he with hyv' | hyx'
  · exact hyv hyv'
  · exact hyx hyx'

private lemma suppressPair_left_edge_not_loop_at_left {G : MultiGraph V E}
    {v x : V} {e : E} (he : G.IsLink e v x) (hxv : x ≠ v) :
    e ∉ G.loopSetAt x := by
  intro hloop
  rcases he.left_eq_or_eq hloop.2 with hvx | hvx
  · exact hxv hvx.symm
  · exact hxv hvx.symm

private lemma suppressPair_right_edge_not_loop_at_right {G : MultiGraph V E}
    {v y : V} {f : E} (hf : G.IsLink f v y) (hyv : y ≠ v) :
    f ∉ G.loopSetAt y := by
  intro hloop
  rcases hf.left_eq_or_eq hloop.2 with hvy | hvy
  · exact hyv hvy.symm
  · exact hyv hvy.symm

private lemma not_loopAt_of_isLink_ne {G : MultiGraph V E}
    {e : E} {a u w : V} (h : G.IsLink e u w) (huw : w ≠ u) :
    ¬ G.IsLoopAt e a := by
  intro hloop
  have hua : a = u := hloop.eq_of_inc h.inc_left
  have hwa : a = w := hloop.eq_of_inc h.inc_right
  exact huw (hwa.symm.trans hua)

private noncomputable def suppressPair_incidentEquiv_left_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    {g : StepEdge E // (suppressPair G v x y e f).Incident x g} ≃
      {g : E // G.Incident x g} where
  toFun
    | ⟨Sum.inl old, hg⟩ =>
        let hincOld :
            (suppressPair G v x y e f).Inc (Sum.inl old) x := hg.2
        let hdel :
            (G.deleteVerts ({v} : Set V)).Inc old x :=
          (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := x) (e := e) (f := f) (old := old)).mp hincOld |>.2.2
        ⟨old, ⟨(Graph.deleteVerts_le (G := G) (X := ({v} : Set V))).edgeSet_mono
          hdel.edge_mem, hdel.mono (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))⟩⟩
    | ⟨Sum.inr (), _hg⟩ =>
        ⟨e, ⟨he.edge_mem, he.inc_right⟩⟩
  invFun
    | ⟨g, hg⟩ =>
        letI := Classical.decEq E
        if hge : g = e then
          ⟨Sum.inr (), by
            subst g
            exact suppressPair_new_inc_of_eq_left (G := G)
              (v := v) (x := x) (y := y) (e := e) (f := f) rfl
              he.right_mem hf.right_mem hxv hyv⟩
        else
          have hgf : g ≠ f := by
            intro hgf
            have hincf : G.Incident x f := by
              simpa [hgf] using hg
            exact suppressPair_not_inc_left_of_right_edge (G := G) hf hxv hxy hincf
          ⟨Sum.inl g, suppressPair_old_inc_of_original_inc_not_removed
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            hvef hge hgf hxv hg⟩
  left_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hincOld :
            (suppressPair G v x y e f).Inc (Sum.inl old) x := hg.2
        have hold_ne :
            old ≠ e :=
          (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := x) (e := e) (f := f) (old := old)).mp hincOld |>.1
        simp [hold_ne]
    | inr u =>
        simp
  right_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    by_cases hge : g = e
    · subst g
      simp
    · apply Subtype.ext
      simp [hge]

private noncomputable def suppressPair_loopEquiv_left_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    {g : StepEdge E // g ∈ (suppressPair G v x y e f).loopSetAt x} ≃
      {g : E // g ∈ G.loopSetAt x} where
  toFun g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hloop :
            (suppressPair G v x y e f).IsLoopAt (Sum.inl old) x := hg.2
        have hold :=
          (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := x) (e := e) (f := f) (old := old)).mp hloop
        exact ⟨old, ⟨hold.2.2.1.edge_mem, hold.2.2.1⟩⟩
    | inr u =>
        have hnew :
            x = x ∧ x = y ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := x) (e := e) (f := f)).mp hg.2
        exact False.elim (hxy hnew.2.1)
  invFun g := by
    classical
    rcases g with ⟨g, hg⟩
    have hge : g ≠ e := by
      intro hge
      subst g
      exact suppressPair_left_edge_not_loop_at_left (G := G) he hxv hg
    have hgf : g ≠ f := by
      intro hgf
      subst g
      have hincf : G.Incident x f := ⟨hg.1, hg.2.inc⟩
      exact suppressPair_not_inc_left_of_right_edge (G := G) hf hxv hxy hincf
    exact ⟨Sum.inl g, suppressPair_old_loop_of_original_loop_not_removed
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      hge hgf hxv hg⟩
  left_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hloop :
            (suppressPair G v x y e f).IsLoopAt (Sum.inl old) x := hg.2
        have hold_ne :
            old ≠ e :=
          (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := x) (e := e) (f := f) (old := old)).mp hloop |>.1
        simp [hold_ne]
    | inr u =>
        have hnew :
            x = x ∧ x = y ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := x) (e := e) (f := f)).mp hg.2
        exact False.elim (hxy hnew.2.1)
  right_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    simp

lemma suppressPair_diestelDegree_eq_left_nonloop {G : MultiGraph V E}
    [Finite E] {v x y : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    (suppressPair G v x y e f).diestelDegree x = G.diestelDegree x := by
  classical
  rw [diestelDegree_eq_card_degreeToken
      (suppressPair G v x y e f) x,
    diestelDegree_eq_card_degreeToken G x]
  exact Nat.card_congr
    (Equiv.sumCongr
      (suppressPair_incidentEquiv_left_nonloop
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        he hf hvef hxv hyv hxy)
      (suppressPair_loopEquiv_left_nonloop
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        he hf hxv hyv hxy))

private noncomputable def suppressPair_incidentEquiv_right_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    {g : StepEdge E // (suppressPair G v x y e f).Incident y g} ≃
      {g : E // G.Incident y g} where
  toFun
    | ⟨Sum.inl old, hg⟩ =>
        let hincOld :
            (suppressPair G v x y e f).Inc (Sum.inl old) y := hg.2
        let hdel :
            (G.deleteVerts ({v} : Set V)).Inc old y :=
          (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := y) (e := e) (f := f) (old := old)).mp hincOld |>.2.2
        ⟨old, ⟨(Graph.deleteVerts_le (G := G) (X := ({v} : Set V))).edgeSet_mono
          hdel.edge_mem, hdel.mono (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))⟩⟩
    | ⟨Sum.inr (), _hg⟩ =>
        ⟨f, ⟨hf.edge_mem, hf.inc_right⟩⟩
  invFun
    | ⟨g, hg⟩ =>
        letI := Classical.decEq E
        if hgf : g = f then
          ⟨Sum.inr (), by
            subst g
            exact suppressPair_new_inc_of_eq_right (G := G)
              (v := v) (x := x) (y := y) (e := e) (f := f) rfl
              he.right_mem hf.right_mem hxv hyv⟩
        else
          have hge : g ≠ e := by
            intro hge
            have hince : G.Incident y e := by
              simpa [hge] using hg
            exact suppressPair_not_inc_right_of_left_edge (G := G) he hyv
              (Ne.symm hxy) hince
          ⟨Sum.inl g, suppressPair_old_inc_of_original_inc_not_removed
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            hvef hge hgf hyv hg⟩
  left_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hincOld :
            (suppressPair G v x y e f).Inc (Sum.inl old) y := hg.2
        have hold_ne :
            old ≠ f :=
          (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := y) (e := e) (f := f) (old := old)).mp hincOld |>.2.1
        simp [hold_ne]
    | inr u =>
        simp
  right_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    by_cases hgf : g = f
    · subst g
      simp
    · apply Subtype.ext
      simp [hgf]

private noncomputable def suppressPair_loopEquiv_right_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    {g : StepEdge E // g ∈ (suppressPair G v x y e f).loopSetAt y} ≃
      {g : E // g ∈ G.loopSetAt y} where
  toFun g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hloop :
            (suppressPair G v x y e f).IsLoopAt (Sum.inl old) y := hg.2
        have hold :=
          (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := y) (e := e) (f := f) (old := old)).mp hloop
        exact ⟨old, ⟨hold.2.2.1.edge_mem, hold.2.2.1⟩⟩
    | inr u =>
        have hnew :
            y = x ∧ y = y ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := y) (e := e) (f := f)).mp hg.2
        exact False.elim (hxy hnew.1.symm)
  invFun g := by
    classical
    rcases g with ⟨g, hg⟩
    have hgf : g ≠ f := by
      intro hgf
      subst g
      exact suppressPair_right_edge_not_loop_at_right (G := G) hf hyv hg
    have hge : g ≠ e := by
      intro hge
      subst g
      have hince : G.Incident y e := ⟨hg.1, hg.2.inc⟩
      exact suppressPair_not_inc_right_of_left_edge (G := G) he hyv
        (Ne.symm hxy) hince
    exact ⟨Sum.inl g, suppressPair_old_loop_of_original_loop_not_removed
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      hge hgf hyv hg⟩
  left_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hloop :
            (suppressPair G v x y e f).IsLoopAt (Sum.inl old) y := hg.2
        have hold_ne :
            old ≠ f :=
          (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := y) (e := e) (f := f) (old := old)).mp hloop |>.2.1
        simp [hold_ne]
    | inr u =>
        have hnew :
            y = x ∧ y = y ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := y) (e := e) (f := f)).mp hg.2
        exact False.elim (hxy hnew.1.symm)
  right_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    simp

lemma suppressPair_diestelDegree_eq_right_nonloop {G : MultiGraph V E}
    [Finite E] {v x y : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    (suppressPair G v x y e f).diestelDegree y = G.diestelDegree y := by
  classical
  rw [diestelDegree_eq_card_degreeToken
      (suppressPair G v x y e f) y,
    diestelDegree_eq_card_degreeToken G y]
  exact Nat.card_congr
    (Equiv.sumCongr
      (suppressPair_incidentEquiv_right_nonloop
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        he hf hvef hxv hyv hxy)
      (suppressPair_loopEquiv_right_nonloop
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        he hf hxv hyv hxy))

private noncomputable def suppressPair_degreeTokenEquiv_loop_endpoint
    {G : MultiGraph V E} {v x : V} {e f : E}
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) :
    DegreeToken (suppressPair G v x x e f) x ≃ DegreeToken G x where
  toFun
    | Sum.inl ⟨Sum.inl old, hg⟩ =>
        let hincOld :
            (suppressPair G v x x e f).Inc (Sum.inl old) x := hg.2
        let hdel :
            (G.deleteVerts ({v} : Set V)).Inc old x :=
          (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := x)
            (a := x) (e := e) (f := f) (old := old)).mp hincOld |>.2.2
        Sum.inl ⟨old, ⟨(Graph.deleteVerts_le (G := G) (X := ({v} : Set V))).edgeSet_mono
          hdel.edge_mem, hdel.mono (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))⟩⟩
    | Sum.inl ⟨Sum.inr (), _hg⟩ =>
        Sum.inl ⟨e, ⟨he.edge_mem, he.inc_right⟩⟩
    | Sum.inr ⟨Sum.inl old, hg⟩ =>
        let hloop :
            (suppressPair G v x x e f).IsLoopAt (Sum.inl old) x := hg.2
        let hold :=
          (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := x)
            (a := x) (e := e) (f := f) (old := old)).mp hloop
        Sum.inr ⟨old, ⟨hold.2.2.1.edge_mem, hold.2.2.1⟩⟩
    | Sum.inr ⟨Sum.inr (), _hg⟩ =>
        Sum.inl ⟨f, ⟨hf.edge_mem, hf.inc_right⟩⟩
  invFun
    | Sum.inl ⟨g, hg⟩ =>
        letI := Classical.decEq E
        if hge : g = e then
          Sum.inl ⟨Sum.inr (), by
            subst g
            exact suppressPair_new_inc_of_eq_left (G := G)
              (v := v) (x := x) (y := x) (e := e) (f := f) rfl
              he.right_mem hf.right_mem hxv hxv⟩
        else if hgf : g = f then
          Sum.inr ⟨Sum.inr (), by
            subst g
            exact suppressPair_new_loop_incident (G := G)
              (v := v) (x := x) (y := x) (e := e) (f := f)
              rfl rfl he.right_mem hf.right_mem hxv hxv⟩
        else
          Sum.inl ⟨Sum.inl g, suppressPair_old_inc_of_original_inc_not_removed
            (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
            hvef hge hgf hxv hg⟩
    | Sum.inr ⟨g, hg⟩ =>
        have hge : g ≠ e := by
          intro hge
          subst g
          exact suppressPair_left_edge_not_loop_at_left (G := G) he hxv hg
        have hgf : g ≠ f := by
          intro hgf
          subst g
          exact suppressPair_right_edge_not_loop_at_right (G := G) hf hxv hg
        Sum.inr ⟨Sum.inl g, suppressPair_old_loop_of_original_loop_not_removed
          (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
          hge hgf hxv hg⟩
  left_inv g := by
    classical
    rcases g with (⟨g, hg⟩ | ⟨g, hg⟩)
    · cases g with
      | inl old =>
          have hincOld :
              (suppressPair G v x x e f).Inc (Sum.inl old) x := hg.2
          have hold_ne_e :
              old ≠ e :=
            (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := x)
              (a := x) (e := e) (f := f) (old := old)).mp hincOld |>.1
          have hold_ne_f :
              old ≠ f :=
            (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := x)
              (a := x) (e := e) (f := f) (old := old)).mp hincOld |>.2.1
          simp [hold_ne_e, hold_ne_f]
      | inr u =>
          simp
    · cases g with
      | inl old =>
          have hloop :
              (suppressPair G v x x e f).IsLoopAt (Sum.inl old) x := hg.2
          have hold_ne_e :
              old ≠ e :=
            (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := x)
              (a := x) (e := e) (f := f) (old := old)).mp hloop |>.1
          have hold_ne_f :
              old ≠ f :=
            (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := x)
              (a := x) (e := e) (f := f) (old := old)).mp hloop |>.2.1
          simp [hold_ne_e, hold_ne_f]
      | inr u =>
          cases u
          have hfe : f ≠ e := fun h => hef h.symm
          simp [hfe]
  right_inv g := by
    classical
    rcases g with (⟨g, hg⟩ | ⟨g, hg⟩)
    · by_cases hge : g = e
      · subst g
        simp
      · by_cases hgf : g = f
        · subst g
          simp [hge]
        · simp [hge, hgf]
    · simp

lemma suppressPair_diestelDegree_eq_loop_endpoint {G : MultiGraph V E}
    [Finite E] {v x : V} {e f : E}
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) :
    (suppressPair G v x x e f).diestelDegree x = G.diestelDegree x := by
  classical
  rw [diestelDegree_eq_card_degreeToken
      (suppressPair G v x x e f) x,
    diestelDegree_eq_card_degreeToken G x]
  exact Nat.card_congr
    (suppressPair_degreeTokenEquiv_loop_endpoint
      (G := G) (v := v) (x := x) (e := e) (f := f)
      hef he hf hvef hxv)

private noncomputable def suppressPair_incidentEquiv_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    {g : StepEdge E // (suppressPair G v x y e f).Incident a g} ≃
      {g : E // G.Incident a g} where
  toFun g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hincOld :
            (suppressPair G v x y e f).Inc (Sum.inl old) a := hg.2
        have hdel :
            (G.deleteVerts ({v} : Set V)).Inc old a :=
          (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := a) (e := e) (f := f) (old := old)).mp hincOld |>.2.2
        exact ⟨old, ⟨(Graph.deleteVerts_le (G := G) (X := ({v} : Set V))).edgeSet_mono
          hdel.edge_mem, hdel.mono (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))⟩⟩
    | inr u =>
        have hnew :
            (a = x ∨ a = y) ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := a) (e := e) (f := f)).mp hg.2
        exact False.elim (hnew.1.elim hax hay)
  invFun g := by
    classical
    rcases g with ⟨g, hg⟩
    have hne := suppressPair_edge_ne_of_inc_not_endpoint
      (G := G) (v := v) (x := x) (y := y) (a := a)
      (e := e) (f := f) he hf hav hax hay hg
    let b : V := hg.2.other
    have hlink : G.IsLink g a b := hg.2.isLink_other
    have hbv : b ≠ v :=
      suppressPair_other_endpoint_ne_v (G := G) (v := v)
        (x := x) (y := y) (a := a) (b := b) (e := e) (f := f)
        hvef hne.1 hne.2 hlink
    have hdel : (G.deleteVerts ({v} : Set V)).Inc g a := by
      refine ⟨b, ?_⟩
      rw [Graph.deleteVerts_isLink]
      exact ⟨hlink, by simpa using hav, by simpa using hbv⟩
    have hHinc : (suppressPair G v x y e f).Inc (Sum.inl g) a :=
      (suppressPair_old_inc_iff (G := G) (v := v) (x := x) (y := y)
        (a := a) (e := e) (f := f) (old := g)).mpr ⟨hne.1, hne.2, hdel⟩
    exact ⟨Sum.inl g, ⟨hHinc.edge_mem, hHinc⟩⟩
  left_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        rfl
    | inr u =>
        have hnew :
            (a = x ∨ a = y) ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_inc_iff (G := G) (v := v) (x := x) (y := y)
            (a := a) (e := e) (f := f)).mp hg.2
        exact False.elim (hnew.1.elim hax hay)
  right_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    rfl

private lemma suppressPair_edge_ne_of_loop_not_v {G : MultiGraph V E}
    {v x y a : V} {e f g : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hav : a ≠ v) (hg : g ∈ G.loopSetAt a) :
    g ≠ e ∧ g ≠ f := by
  constructor
  · intro hge
    subst g
    rcases he.left_eq_or_eq hg.2 with hva | hva
    · exact hav hva.symm
    · exact hav hva.symm
  · intro hgf
    subst g
    rcases hf.left_eq_or_eq hg.2 with hva | hva
    · exact hav hva.symm
    · exact hav hva.symm

private noncomputable def suppressPair_loopEquiv_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    {g : StepEdge E // g ∈ (suppressPair G v x y e f).loopSetAt a} ≃
      {g : E // g ∈ G.loopSetAt a} where
  toFun g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        have hloop :
            (suppressPair G v x y e f).IsLoopAt (Sum.inl old) a := hg.2
        have hold :=
          (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := a) (e := e) (f := f) (old := old)).mp hloop
        exact ⟨old, ⟨hold.2.2.1.edge_mem, hold.2.2.1⟩⟩
    | inr u =>
        have hnew :
            a = x ∧ a = y ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := a) (e := e) (f := f)).mp hg.2
        exact False.elim (hax hnew.1)
  invFun g := by
    classical
    rcases g with ⟨g, hg⟩
    have hne := suppressPair_edge_ne_of_loop_not_v
      (G := G) (v := v) (x := x) (y := y) (a := a)
      (e := e) (f := f) he hf hav hg
    have hHloop : (suppressPair G v x y e f).IsLoopAt (Sum.inl g) a :=
      (suppressPair_old_loopAt_iff (G := G) (v := v) (x := x) (y := y)
        (a := a) (e := e) (f := f) (old := g)).mpr
        ⟨hne.1, hne.2, hg.2, hav⟩
    exact ⟨Sum.inl g, ⟨hHloop.edge_mem, hHloop⟩⟩
  left_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    cases g with
    | inl old =>
        rfl
    | inr u =>
        have hnew :
            a = x ∧ a = y ∧
              x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v :=
          (suppressPair_new_loopAt_iff (G := G) (v := v) (x := x) (y := y)
            (a := a) (e := e) (f := f)).mp hg.2
        exact False.elim (hax hnew.1)
  right_inv g := by
    classical
    rcases g with ⟨g, hg⟩
    rfl

lemma suppressPair_diestelDegree_eq_of_not_endpoint {G : MultiGraph V E}
    [Finite E] {v x y a : V} {e f : E}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    (suppressPair G v x y e f).diestelDegree a = G.diestelDegree a := by
  classical
  change
    Nat.card {g : StepEdge E // (suppressPair G v x y e f).Incident a g} +
        Nat.card {g : StepEdge E // g ∈ (suppressPair G v x y e f).loopSetAt a} =
      Nat.card {g : E // G.Incident a g} +
        Nat.card {g : E // g ∈ G.loopSetAt a}
  rw [Nat.card_congr (suppressPair_incidentEquiv_of_not_endpoint
      (G := G) (v := v) (x := x) (y := y) (a := a)
      (e := e) (f := f) he hf hvef hav hax hay),
    Nat.card_congr (suppressPair_loopEquiv_of_not_endpoint
      (G := G) (v := v) (x := x) (y := y) (a := a)
      (e := e) (f := f) he hf hav hax hay)]

lemma suppressPair_isDiestelCubic {G : MultiGraph V E}
    [Finite E] (hG : G.IsDiestelCubic)
    {v x y : V} {e f : E}
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (suppressPair G v x y e f).IsDiestelCubic := by
  intro a ha
  rw [suppressPair_vertexSet] at ha
  have haG : a ∈ G.vertexSet := ha.1
  have hav : a ≠ v := by
    intro hav
    exact ha.2 (by simp [hav])
  have hGa : G.diestelDegree a = 3 := hG a haG
  by_cases hxy : x = y
  · subst y
    by_cases hax : a = x
    · subst a
      rw [suppressPair_diestelDegree_eq_loop_endpoint
        (G := G) (v := v) (x := x) (e := e) (f := f)
        hef he hf hvef hxv]
      exact hG x he.right_mem
    · rw [suppressPair_diestelDegree_eq_of_not_endpoint
        (G := G) (v := v) (x := x) (y := x) (a := a)
        (e := e) (f := f) he hf hvef hav hax hax]
      exact hGa
  · by_cases hax : a = x
    · subst a
      rw [suppressPair_diestelDegree_eq_left_nonloop
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        he hf hvef hxv hyv hxy]
      exact hG x he.right_mem
    · by_cases hay : a = y
      · subst a
        rw [suppressPair_diestelDegree_eq_right_nonloop
          (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
          he hf hvef hxv hyv hxy]
        exact hG y hf.right_mem
      · rw [suppressPair_diestelDegree_eq_of_not_endpoint
          (G := G) (v := v) (x := x) (y := y) (a := a)
          (e := e) (f := f) he hf hvef hav hax hay]
        exact hGa

/-- Old edge labels appearing in an edge set of a suppressed graph. -/
def oldEdgeSupport (F : Set (StepEdge E)) : Set E :=
  {e : E | Sum.inl e ∈ F}

/-- Expand a suppressed edge set by replacing the new edge with the two old edges. -/
def expandedEdgeSupport (F : Set (StepEdge E)) (e f : E) : Set E :=
  oldEdgeSupport (E := E) F ∪ {e, f}

/-- Expand a suppressed cycle support by adding back the suppressed vertex. -/
def expandedSupport (S : Set V) (v : V) : Set V :=
  S ∪ {v}

@[simp]
lemma mem_oldEdgeSupport {F : Set (StepEdge E)} {e : E} :
    e ∈ oldEdgeSupport (E := E) F ↔ Sum.inl e ∈ F :=
  Iff.rfl

@[simp]
lemma mem_expandedEdgeSupport {F : Set (StepEdge E)} {e f g : E} :
    g ∈ expandedEdgeSupport (E := E) F e f ↔
      Sum.inl g ∈ F ∨ g = e ∨ g = f := by
  simp [expandedEdgeSupport, oldEdgeSupport, Set.mem_insert_iff]
  tauto

@[simp]
lemma mem_expandedSupport {S : Set V} {v a : V} :
    a ∈ expandedSupport S v ↔ a ∈ S ∨ a = v := by
  simp [expandedSupport]
  tauto

lemma oldEdgeSupport_finite {F : Set (StepEdge E)} (hF : F.Finite) :
    (oldEdgeSupport (E := E) F).Finite := by
  classical
  change (Sum.inl ⁻¹' F).Finite
  exact hF.preimage (Sum.inl_injective.injOn)

lemma expandedEdgeSupport_finite {F : Set (StepEdge E)}
    (hF : F.Finite) (e f : E) :
    (expandedEdgeSupport (E := E) F e f).Finite := by
  exact (oldEdgeSupport_finite (E := E) hF).union
    ((Set.finite_singleton f).insert e)

private lemma reachable_map_of_adj_reachable
    {α : Type*} {β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (φ : α → β)
    (hmap : ∀ a b : α, G.Adj a b → H.Reachable (φ a) (φ b))
    {a b : α} (h : G.Reachable a b) :
    H.Reachable (φ a) (φ b) := by
  rcases h with ⟨w⟩
  induction w with
  | nil =>
      exact SimpleGraph.Reachable.rfl
  | cons hadj w ih =>
      exact (hmap _ _ hadj).trans ih

lemma original_isLink_of_suppressPair_old_isLink {G : MultiGraph V E}
    {v x y a b : V} {e f old : E}
    (h : (suppressPair G v x y e f).IsLink (Sum.inl old) a b) :
    G.IsLink old a b :=
  h.2.2.1

lemma original_edge_mem_of_suppressPair_old_edge_mem {G : MultiGraph V E}
    {v x y : V} {e f old : E}
    (h : Sum.inl old ∈ (suppressPair G v x y e f).edgeSet) :
    old ∈ G.edgeSet := by
  obtain ⟨a, b, hlink⟩ :=
    Graph.exists_isLink_of_mem_edgeSet (G := suppressPair G v x y e f) h
  exact (original_isLink_of_suppressPair_old_isLink (G := G) hlink).edge_mem

lemma suppressPair_old_edge_ne_left_right_of_cycle_mem {G : MultiGraph V E}
    {v x y : V} {e f old : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hold : Sum.inl old ∈ C.edgeSupport) :
    old ≠ e ∧ old ≠ f := by
  have heH : Sum.inl old ∈ (suppressPair G v x y e f).edgeSet :=
    (C.edges_inside hold).1
  obtain ⟨a, b, hlink⟩ :=
    Graph.exists_isLink_of_mem_edgeSet
      (G := suppressPair G v x y e f) heH
  exact ⟨hlink.1, hlink.2.1⟩

lemma suppressPair_left_not_mem_oldEdgeSupport_of_cycle {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn) :
    e ∉ oldEdgeSupport (E := E) C.edgeSupport := by
  intro heold
  exact (suppressPair_old_edge_ne_left_right_of_cycle_mem
    (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
    C heold).1 rfl

lemma suppressPair_right_not_mem_oldEdgeSupport_of_cycle {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn) :
    f ∉ oldEdgeSupport (E := E) C.edgeSupport := by
  intro hfold
  exact (suppressPair_old_edge_ne_left_right_of_cycle_mem
    (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
    C hfold).2 rfl

lemma original_incident_of_suppressPair_old_incident {G : MultiGraph V E}
    {v x y a : V} {e f old : E}
    (h : (suppressPair G v x y e f).Incident a (Sum.inl old)) :
    G.Incident a old := by
  have hinc :
      (suppressPair G v x y e f).Inc (Sum.inl old) a := h.2
  obtain ⟨b, hlink⟩ := hinc
  exact ⟨(original_isLink_of_suppressPair_old_isLink (G := G) hlink).edge_mem,
    (original_isLink_of_suppressPair_old_isLink (G := G) hlink).inc_left⟩

lemma suppressPair_old_inc_of_original_inc_of_old_edge_mem {G : MultiGraph V E}
    {v x y a : V} {e f old : E}
    (heH : Sum.inl old ∈ (suppressPair G v x y e f).edgeSet)
    (hinc : G.Inc old a) :
    (suppressPair G v x y e f).Inc (Sum.inl old) a := by
  obtain ⟨p, q, hlinkH⟩ :=
    Graph.exists_isLink_of_mem_edgeSet
      (G := suppressPair G v x y e f) heH
  have hlinkG : G.IsLink old p q :=
    original_isLink_of_suppressPair_old_isLink (G := G) hlinkH
  rcases hinc.eq_or_eq_of_isLink hlinkG with rfl | rfl
  · exact hlinkH.inc_left
  · exact hlinkH.inc_right

lemma suppressPair_old_loopAt_of_original_loopAt_of_old_edge_mem {G : MultiGraph V E}
    {v x y a : V} {e f old : E}
    (heH : Sum.inl old ∈ (suppressPair G v x y e f).edgeSet)
    (hloop : G.IsLoopAt old a) :
    (suppressPair G v x y e f).IsLoopAt (Sum.inl old) a := by
  obtain ⟨p, q, hlinkH⟩ :=
    Graph.exists_isLink_of_mem_edgeSet
      (G := suppressPair G v x y e f) heH
  have hlinkG : G.IsLink old p q :=
    original_isLink_of_suppressPair_old_isLink (G := G) hlinkH
  have hp : a = p := hloop.eq_of_inc hlinkG.inc_left
  have hq : a = q := hloop.eq_of_inc hlinkG.inc_right
  subst p
  subst q
  exact hlinkH

private noncomputable def oldEdgeSupport_incEquiv
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hNoNew : Sum.inr () ∉ C.edgeSupport) :
    {g : oldEdgeSupport (E := E) C.edgeSupport // G.Inc g.1 a} ≃
      {g : C.edgeSupport // (suppressPair G v x y e f).Inc g.1 a} where
  toFun g := by
    rcases g with ⟨⟨g, hgC⟩, hginc⟩
    have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
      (C.edges_inside hgC).1
    exact ⟨⟨Sum.inl g, hgC⟩,
      suppressPair_old_inc_of_original_inc_of_old_edge_mem
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        heH hginc⟩
  invFun g := by
    rcases g with ⟨⟨g, hgC⟩, hginc⟩
    cases g with
    | inl old =>
        exact ⟨⟨old, hgC⟩,
          (original_incident_of_suppressPair_old_incident
            (G := G) (v := v) (x := x) (y := y)
            (e := e) (f := f)
            ⟨hginc.edge_mem, hginc⟩).2⟩
    | inr u =>
        exact False.elim (hNoNew (by simpa using hgC))
  left_inv g := by
    rcases g with ⟨⟨g, hgC⟩, hginc⟩
    rfl
  right_inv g := by
    rcases g with ⟨⟨g, hgC⟩, hginc⟩
    cases g with
    | inl old =>
        rfl
    | inr u =>
        exact False.elim (hNoNew (by simpa using hgC))

private noncomputable def oldEdgeSupport_loopEquiv
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hNoNew : Sum.inr () ∉ C.edgeSupport) :
    {g : oldEdgeSupport (E := E) C.edgeSupport // G.IsLoopAt g.1 a} ≃
      {g : C.edgeSupport // (suppressPair G v x y e f).IsLoopAt g.1 a} where
  toFun g := by
    rcases g with ⟨⟨g, hgC⟩, hgloop⟩
    have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
      (C.edges_inside hgC).1
    exact ⟨⟨Sum.inl g, hgC⟩,
      suppressPair_old_loopAt_of_original_loopAt_of_old_edge_mem
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        heH hgloop⟩
  invFun g := by
    rcases g with ⟨⟨g, hgC⟩, hgloop⟩
    cases g with
    | inl old =>
        have hloopG : G.IsLoopAt old a :=
          original_isLink_of_suppressPair_old_isLink (G := G) hgloop
        exact ⟨⟨old, hgC⟩, hloopG⟩
    | inr u =>
        exact False.elim (hNoNew (by simpa using hgC))
  left_inv g := by
    rcases g with ⟨⟨g, hgC⟩, hgloop⟩
    rfl
  right_inv g := by
    rcases g with ⟨⟨g, hgC⟩, hgloop⟩
    cases g with
    | inl old =>
        rfl
    | inr u =>
        exact False.elim (hNoNew (by simpa using hgC))

private noncomputable def suppressPair_expanded_degreeTokenTo_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) a →
      DegreeTokenInEdgeSet (suppressPair G v x y e f) C.edgeSupport a := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgF⟩, hginc⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inl ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_inc_of_original_inc_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            heH hginc⟩
      else if hge : g = e then
        subst g
        have hfalse : False := by
          rcases hginc.eq_or_eq_of_isLink he with hav' | hax'
          · exact hav hav'
          · exact hax hax'
        exact False.elim hfalse
      else if hgf : g = f then
        subst g
        have hfalse : False := by
          rcases hginc.eq_or_eq_of_isLink hf with hav' | hay'
          · exact hav hav'
          · exact hay hay'
        exact False.elim hfalse
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgF⟩, hgloop⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inr ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_loopAt_of_original_loopAt_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            heH hgloop⟩
      else if hge : g = e then
        subst g
        exact False.elim
          (not_loopAt_of_isLink_ne (G := G) he hxv hgloop)
      else if hgf : g = f then
        subst g
        exact False.elim
          (not_loopAt_of_isLink_ne (G := G) hf hyv hgloop)
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse

private lemma suppressPair_expanded_inc_old_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f g : E}
    {C : (suppressPair G v x y e f).DiestelCycleIn}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hginc : G.Inc g a) :
    Sum.inl g ∈ C.edgeSupport := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact hold
  · subst g
    rcases hginc.eq_or_eq_of_isLink he with hav' | hax'
    · exact (hav hav').elim
    · exact (hax hax').elim
  · subst g
    rcases hginc.eq_or_eq_of_isLink hf with hav' | hay'
    · exact (hav hav').elim
    · exact (hay hay').elim

private lemma suppressPair_expanded_loop_old_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f g : E}
    {C : (suppressPair G v x y e f).DiestelCycleIn}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hgloop : G.IsLoopAt g a) :
    Sum.inl g ∈ C.edgeSupport := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact hold
  · subst g
    exact (not_loopAt_of_isLink_ne (G := G) he hxv hgloop).elim
  · subst g
    exact (not_loopAt_of_isLink_ne (G := G) hf hyv hgloop).elim

private lemma suppressPair_expanded_degreeTokenTo_of_not_endpoint_injective
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    Function.Injective
      (suppressPair_expanded_degreeTokenTo_of_not_endpoint
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C he hf hxv hyv hav hax hay) := by
  classical
  intro p q hpq
  cases p with
  | inl pInc =>
      cases q with
      | inl qInc =>
          rcases pInc with ⟨⟨gp, hgpF⟩, hgpinc⟩
          rcases qInc with ⟨⟨gq, hgqF⟩, hgqinc⟩
          have hpold :
              Sum.inl gp ∈ C.edgeSupport :=
            suppressPair_expanded_inc_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hav hax hay hgpF hgpinc
          have hqold :
              Sum.inl gq ∈ C.edgeSupport :=
            suppressPair_expanded_inc_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hav hax hay hgqF hgqinc
          dsimp [suppressPair_expanded_degreeTokenTo_of_not_endpoint] at hpq
          rw [dif_pos hpold, dif_pos hqold] at hpq
          injection hpq with hsub
          have hlabelStep :
              (Sum.inl gp : StepEdge E) = Sum.inl gq :=
            congrArg (fun z => z.1.1) hsub
          have hlabel : gp = gq := Sum.inl_injective hlabelStep
          subst gq
          simp
      | inr qLoop =>
          rcases pInc with ⟨⟨gp, hgpF⟩, hgpinc⟩
          rcases qLoop with ⟨⟨gq, hgqF⟩, hgqloop⟩
          have hpold :
              Sum.inl gp ∈ C.edgeSupport :=
            suppressPair_expanded_inc_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hav hax hay hgpF hgpinc
          have hqold :
              Sum.inl gq ∈ C.edgeSupport :=
            suppressPair_expanded_loop_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hxv hyv hgqF hgqloop
          dsimp [suppressPair_expanded_degreeTokenTo_of_not_endpoint] at hpq
          rw [dif_pos hpold, dif_pos hqold] at hpq
          cases hpq
  | inr pLoop =>
      cases q with
      | inl qInc =>
          rcases pLoop with ⟨⟨gp, hgpF⟩, hgploop⟩
          rcases qInc with ⟨⟨gq, hgqF⟩, hgqinc⟩
          have hpold :
              Sum.inl gp ∈ C.edgeSupport :=
            suppressPair_expanded_loop_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hxv hyv hgpF hgploop
          have hqold :
              Sum.inl gq ∈ C.edgeSupport :=
            suppressPair_expanded_inc_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hav hax hay hgqF hgqinc
          dsimp [suppressPair_expanded_degreeTokenTo_of_not_endpoint] at hpq
          rw [dif_pos hpold, dif_pos hqold] at hpq
          cases hpq
      | inr qLoop =>
          rcases pLoop with ⟨⟨gp, hgpF⟩, hgploop⟩
          rcases qLoop with ⟨⟨gq, hgqF⟩, hgqloop⟩
          have hpold :
              Sum.inl gp ∈ C.edgeSupport :=
            suppressPair_expanded_loop_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hxv hyv hgpF hgploop
          have hqold :
              Sum.inl gq ∈ C.edgeSupport :=
            suppressPair_expanded_loop_old_of_not_endpoint
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) he hf hxv hyv hgqF hgqloop
          dsimp [suppressPair_expanded_degreeTokenTo_of_not_endpoint] at hpq
          rw [dif_pos hpold, dif_pos hqold] at hpq
          injection hpq with hsub
          have hlabelStep :
              (Sum.inl gp : StepEdge E) = Sum.inl gq :=
            congrArg (fun z => z.1.1) hsub
          have hlabel : gp = gq := Sum.inl_injective hlabelStep
          subst gq
          simp

private noncomputable def suppressPair_expanded_degreeTokenFrom_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    DegreeTokenInEdgeSet (suppressPair G v x y e f) C.edgeSupport a →
      DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) a := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgC⟩, hginc⟩
      cases g with
      | inl old =>
          exact Sum.inl ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            (original_incident_of_suppressPair_old_incident
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f)
              ⟨hginc.edge_mem, hginc⟩).2⟩
      | inr u =>
          have hnew :=
            (suppressPair_new_inc_iff (G := G) (v := v)
              (x := x) (y := y) (a := a) (e := e) (f := f)).mp hginc
          have hfalse : False := by
            rcases hnew.1 with hax' | hay'
            · exact hax hax'
            · exact hay hay'
          exact False.elim hfalse
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgC⟩, hgloop⟩
      cases g with
      | inl old =>
          have hloopG : G.IsLoopAt old a :=
            original_isLink_of_suppressPair_old_isLink (G := G) hgloop
          exact Sum.inr ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            hloopG⟩
      | inr u =>
          have hnew :=
            (suppressPair_new_loopAt_iff (G := G) (v := v)
              (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgloop
          exact False.elim (hax hnew.1)

private lemma suppressPair_expanded_degreeTokenFrom_of_not_endpoint_injective
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    Function.Injective
      (suppressPair_expanded_degreeTokenFrom_of_not_endpoint
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C hav hax hay) := by
  classical
  intro p q hpq
  cases p with
  | inl pInc =>
      rcases pInc with ⟨⟨gp, hgpC⟩, hgpinc⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_of_not_endpoint] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  have hnew :=
                    (suppressPair_new_inc_iff (G := G) (v := v)
                      (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgqinc
                  rcases hnew.1 with hax' | hay'
                  · exact (hax hax').elim
                  · exact (hay hay').elim
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_of_not_endpoint] at hpq
                  simp at hpq
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgqloop
                  exact (hax hnew.1).elim
      | inr u =>
          have hnew :=
            (suppressPair_new_inc_iff (G := G) (v := v)
              (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgpinc
          rcases hnew.1 with hax' | hay'
          · exact (hax hax').elim
          · exact (hay hay').elim
  | inr pLoop =>
      rcases pLoop with ⟨⟨gp, hgpC⟩, hgploop⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_of_not_endpoint] at hpq
                  simp at hpq
              | inr u =>
                  have hnew :=
                    (suppressPair_new_inc_iff (G := G) (v := v)
                      (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgqinc
                  rcases hnew.1 with hax' | hay'
                  · exact (hax hax').elim
                  · exact (hay hay').elim
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_of_not_endpoint] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgqloop
                  exact (hax hnew.1).elim
      | inr u =>
          have hnew :=
            (suppressPair_new_loopAt_iff (G := G) (v := v)
              (x := x) (y := y) (a := a) (e := e) (f := f)).mp hgploop
          exact (hax hnew.1).elim

private lemma suppressPair_expanded_degreeToken_card_eq_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    Nat.card (DegreeTokenInEdgeSet G
      (expandedEdgeSupport (E := E) C.edgeSupport e f) a) =
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
        C.edgeSupport a) := by
  classical
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  haveI : Finite (expandedEdgeSupport (E := E) C.edgeSupport e f) :=
    Set.Finite.to_subtype
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f)
  have hle₁ :
      Nat.card (DegreeTokenInEdgeSet G
        (expandedEdgeSupport (E := E) C.edgeSupport e f) a) ≤
        Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
          C.edgeSupport a) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenTo_of_not_endpoint
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C he hf hxv hyv hav hax hay)
      (suppressPair_expanded_degreeTokenTo_of_not_endpoint_injective
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C he hf hxv hyv hav hax hay)
  have hle₂ :
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
        C.edgeSupport a) ≤
        Nat.card (DegreeTokenInEdgeSet G
          (expandedEdgeSupport (E := E) C.edgeSupport e f) a) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenFrom_of_not_endpoint
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C hav hax hay)
      (suppressPair_expanded_degreeTokenFrom_of_not_endpoint_injective
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C hav hax hay)
  omega

private lemma suppressPair_expanded_diestelDegreeInEdgeSet_eq_of_not_endpoint
    {G : MultiGraph V E} {v x y a : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) :
    G.diestelDegreeInEdgeSet
        (expandedEdgeSupport (E := E) C.edgeSupport e f) a =
      (suppressPair G v x y e f).diestelDegreeInEdgeSet
        C.edgeSupport a := by
  rw [diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := G)
      (F := expandedEdgeSupport (E := E) C.edgeSupport e f)
      (v := a)
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f),
    diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := suppressPair G v x y e f)
      (F := C.edgeSupport)
      (v := a)
      C.edgeSupport_finite]
  exact suppressPair_expanded_degreeToken_card_eq_of_not_endpoint
    (G := G) (v := v) (x := x) (y := y) (a := a)
    (e := e) (f := f) C he hf hxv hyv hav hax hay

private lemma original_edge_mem_of_mem_expandedEdgeSupport {G : MultiGraph V E}
    {v x y : V} {e f g : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f) :
    g ∈ G.edgeSet := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact original_edge_mem_of_suppressPair_old_edge_mem
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      ((C.edges_inside hold).1)
  · simpa [hge] using he.edge_mem
  · simpa [hgf] using hf.edge_mem

private lemma expanded_incident_suppressed_vertex_eq_left_or_right
    {G : MultiGraph V E} {v x y : V} {e f g : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hginc : G.Inc g v) :
    g = e ∨ g = f :=
  hvef g ⟨original_edge_mem_of_mem_expandedEdgeSupport
    (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
    C he hf hgF, hginc⟩

private noncomputable def pairIncidentEquivBool {G : MultiGraph V E}
    {a : V} {e f : E} (hef : e ≠ f)
    (heinc : G.Inc e a) (hfinc : G.Inc f a) :
    {g : ({e, f} : Set E) // G.Inc g.1 a} ≃ Bool := by
  classical
  refine
    { toFun := fun g => if g.1.1 = e then false else true
      invFun := fun b =>
        cond b ⟨⟨f, by simp⟩, hfinc⟩ ⟨⟨e, by simp⟩, heinc⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    rcases g with ⟨⟨g, hgmem⟩, hginc⟩
    by_cases hge : g = e
    · subst g
      simp
    · have hgf : g = f := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, hge] using hgmem
      subst g
      simp [hef.symm]
  · intro b
    have hfe : f ≠ e := hef.symm
    cases b <;> simp [hef, hfe]

private lemma pair_incident_card {G : MultiGraph V E}
    {a : V} {e f : E} (hef : e ≠ f)
    (heinc : G.Inc e a) (hfinc : G.Inc f a) :
    Nat.card {g : ({e, f} : Set E) // G.Inc g.1 a} = 2 := by
  classical
  rw [Nat.card_congr (pairIncidentEquivBool (G := G) hef heinc hfinc)]
  rw [Nat.card_eq_fintype_card, Fintype.card_bool]

private noncomputable def expandedIncidentSuppressedVertexEquivPair
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f) :
    {g : expandedEdgeSupport (E := E) C.edgeSupport e f // G.Inc g.1 v} ≃
      {g : ({e, f} : Set E) // G.Inc g.1 v} where
  toFun g := by
    rcases g with ⟨⟨g, hgF⟩, hginc⟩
    exact ⟨⟨g, by
      rcases expanded_incident_suppressed_vertex_eq_left_or_right
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        C he hf hvef hgF hginc with rfl | rfl <;> simp⟩, hginc⟩
  invFun g := by
    rcases g with ⟨⟨g, hgpair⟩, hginc⟩
    exact ⟨⟨g, by
      rcases hgpair with rfl | rfl <;> simp [expandedEdgeSupport]⟩, hginc⟩
  left_inv g := by
    rcases g with ⟨⟨g, hgF⟩, hginc⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    rcases g with ⟨⟨g, hgpair⟩, hginc⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

private lemma expanded_loop_suppressed_vertex_false
    {G : MultiGraph V E} {v x y : V} {e f g : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hgloop : G.IsLoopAt g v) :
    False := by
  rcases expanded_incident_suppressed_vertex_eq_left_or_right
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      C he hf hvef hgF hgloop.inc with hge | hgf
  · subst g
    exact not_loopAt_of_isLink_ne (G := G) he hxv hgloop
  · subst g
    exact not_loopAt_of_isLink_ne (G := G) hf hyv hgloop

private lemma suppressPair_expanded_diestelDegreeInEdgeSet_suppressed_vertex
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    G.diestelDegreeInEdgeSet
      (expandedEdgeSupport (E := E) C.edgeSupport e f) v = 2 := by
  classical
  have hinc :
      Nat.card
          {g : expandedEdgeSupport (E := E) C.edgeSupport e f // G.Inc g.1 v} = 2 := by
    rw [Nat.card_congr
      (expandedIncidentSuppressedVertexEquivPair
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hvef)]
    exact pair_incident_card (G := G) hef he.inc_left hf.inc_left
  have hnoLoop : IsEmpty
      {g : expandedEdgeSupport (E := E) C.edgeSupport e f // G.IsLoopAt g.1 v} := by
    refine ⟨?_⟩
    intro g
    exact expanded_loop_suppressed_vertex_false
      (G := G) (v := v) (x := x) (y := y)
      (e := e) (f := f) C he hf hvef hxv hyv g.1.2 g.2
  simp [diestelDegreeInEdgeSet, hinc]

private noncomputable def suppressPair_expanded_degreeTokenTo_left_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) x →
      DegreeTokenInEdgeSet (suppressPair G v x y e f) C.edgeSupport x := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgF⟩, hginc⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inl ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_inc_of_original_inc_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            heH hginc⟩
      else if hge : g = e then
        subst g
        exact Sum.inl ⟨⟨Sum.inr (), hnew⟩,
          (suppressPair_new_inc_of_eq_left (G := G)
            (v := v) (x := x) (y := y) (a := x)
            (e := e) (f := f) rfl he.right_mem hf.right_mem hxv hyv).2⟩
      else if hgf : g = f then
        subst g
        have hfalse : False :=
          suppressPair_not_inc_left_of_right_edge (G := G) hf hxv hxy
            ⟨hf.edge_mem, hginc⟩
        exact False.elim hfalse
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgF⟩, hgloop⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inr ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_loopAt_of_original_loopAt_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            heH hgloop⟩
      else if hge : g = e then
        subst g
        exact False.elim (suppressPair_left_edge_not_loop_at_left (G := G) he hxv
          ⟨he.edge_mem, hgloop⟩)
      else if hgf : g = f then
        subst g
        exact False.elim
          (not_loopAt_of_isLink_ne (G := G) hf hyv hgloop)
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse

private noncomputable def suppressPair_expanded_degreeTokenFrom_left_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    DegreeTokenInEdgeSet (suppressPair G v x y e f) C.edgeSupport x →
      DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) x := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgC⟩, hginc⟩
      cases g with
      | inl old =>
          exact Sum.inl ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            (original_incident_of_suppressPair_old_incident
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f)
              ⟨hginc.edge_mem, hginc⟩).2⟩
      | inr u =>
          exact Sum.inl ⟨⟨e, by simp [expandedEdgeSupport]⟩, he.inc_right⟩
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgC⟩, hgloop⟩
      cases g with
      | inl old =>
          have hloopG : G.IsLoopAt old x :=
            original_isLink_of_suppressPair_old_isLink (G := G) hgloop
          exact Sum.inr ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            hloopG⟩
      | inr u =>
          have hnew :=
            (suppressPair_new_loopAt_iff (G := G) (v := v)
              (x := x) (y := y) (a := x) (e := e) (f := f)).mp hgloop
          exact False.elim (hxy hnew.2.1)

private lemma suppressPair_expanded_degreeTokenFrom_left_nonloop_injective
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    Function.Injective
      (suppressPair_expanded_degreeTokenFrom_left_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hxv hyv hxy) := by
  classical
  intro p q hpq
  cases p with
  | inl pInc =>
      rcases pInc with ⟨⟨gp, hgpC⟩, hgpinc⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := y)
                    (e := e) (f := f) C hgpC).1
                  exact (hne hpq).elim
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := x) (e := e) (f := f)).mp hgqloop
                  exact (hxy hnew.2.1).elim
      | inr u =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := y)
                    (e := e) (f := f) C hgqC).1
                  exact (hne hpq.symm).elim
              | inr u =>
                  simp
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := x) (e := e) (f := f)).mp hgqloop
                  exact (hxy hnew.2.1).elim
  | inr pLoop =>
      rcases pLoop with ⟨⟨gp, hgpC⟩, hgploop⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_left_nonloop] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := x) (e := e) (f := f)).mp hgqloop
                  exact (hxy hnew.2.1).elim
      | inr u =>
          have hnew :=
            (suppressPair_new_loopAt_iff (G := G) (v := v)
              (x := x) (y := y) (a := x) (e := e) (f := f)).mp hgploop
          exact (hxy hnew.2.1).elim

private lemma suppressPair_expanded_inc_left_nonloop_old_or_left
    {G : MultiGraph V E} {v x y : V} {e f g : E}
    {C : (suppressPair G v x y e f).DiestelCycleIn}
    (hf : G.IsLink f v y) (hxv : x ≠ v) (hxy : x ≠ y)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hginc : G.Inc g x) :
    Sum.inl g ∈ C.edgeSupport ∨ g = e := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact Or.inl hold
  · exact Or.inr hge
  · subst g
    exact (suppressPair_not_inc_left_of_right_edge (G := G) hf hxv hxy
      ⟨hf.edge_mem, hginc⟩).elim

private lemma suppressPair_expanded_loop_left_nonloop_old
    {G : MultiGraph V E} {v x y : V} {e f g : E}
    {C : (suppressPair G v x y e f).DiestelCycleIn}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hgloop : G.IsLoopAt g x) :
    Sum.inl g ∈ C.edgeSupport := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact hold
  · subst g
    exact (suppressPair_left_edge_not_loop_at_left (G := G) he hxv
      ⟨he.edge_mem, hgloop⟩).elim
  · subst g
    exact (not_loopAt_of_isLink_ne (G := G) hf hyv hgloop).elim

private lemma suppressPair_expanded_degreeTokenTo_left_nonloop_injective
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    Function.Injective
      (suppressPair_expanded_degreeTokenTo_left_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C hnew he hf hxv hyv hxy) := by
  classical
  have hnotOldE : Sum.inl e ∉ C.edgeSupport :=
    suppressPair_left_not_mem_oldEdgeSupport_of_cycle
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f) C
  intro p q hpq
  cases p with
  | inl pInc =>
      rcases pInc with ⟨⟨gp, hgpF⟩, hgpinc⟩
      have hpclass :=
        suppressPair_expanded_inc_left_nonloop_old_or_left
          (G := G) (v := v) (x := x) (y := y)
          (e := e) (f := f) (C := C) hf hxv hxy hgpF hgpinc
      cases q with
      | inl qInc =>
          rcases qInc with ⟨⟨gq, hgqF⟩, hgqinc⟩
          have hqclass :=
            suppressPair_expanded_inc_left_nonloop_old_or_left
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) hf hxv hxy hgqF hgqinc
          rcases hpclass with hpold | hpe
          · rcases hqclass with hqold | hqe
            · dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
              rw [dif_pos hpold, dif_pos hqold] at hpq
              injection hpq with hsub
              have hlabelStep :
                  (Sum.inl gp : StepEdge E) = Sum.inl gq :=
                congrArg (fun z => z.1.1) hsub
              have hlabel : gp = gq := Sum.inl_injective hlabelStep
              subst gq
              simp
            · subst gq
              dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
              rw [dif_pos hpold, dif_neg hnotOldE, dif_pos rfl] at hpq
              simp at hpq
          · subst gp
            rcases hqclass with hqold | hqe
            · dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
              rw [dif_neg hnotOldE, dif_pos rfl, dif_pos hqold] at hpq
              simp at hpq
            · subst gq
              simp
      | inr qLoop =>
          rcases qLoop with ⟨⟨gq, hgqF⟩, hgqloop⟩
          have hqold :=
            suppressPair_expanded_loop_left_nonloop_old
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) he hf hxv hyv hgqF hgqloop
          rcases hpclass with hpold | hpe
          · dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
            rw [dif_pos hpold, dif_pos hqold] at hpq
            simp at hpq
          · subst gp
            dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
            rw [dif_neg hnotOldE, dif_pos rfl, dif_pos hqold] at hpq
            simp at hpq
  | inr pLoop =>
      rcases pLoop with ⟨⟨gp, hgpF⟩, hgploop⟩
      have hpold :=
        suppressPair_expanded_loop_left_nonloop_old
          (G := G) (v := v) (x := x) (y := y)
          (e := e) (f := f) (C := C) he hf hxv hyv hgpF hgploop
      cases q with
      | inl qInc =>
          rcases qInc with ⟨⟨gq, hgqF⟩, hgqinc⟩
          have hqclass :=
            suppressPair_expanded_inc_left_nonloop_old_or_left
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) hf hxv hxy hgqF hgqinc
          rcases hqclass with hqold | hqe
          · dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
            rw [dif_pos hpold, dif_pos hqold] at hpq
            simp at hpq
          · subst gq
            dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
            rw [dif_pos hpold, dif_neg hnotOldE, dif_pos rfl] at hpq
            simp at hpq
      | inr qLoop =>
          rcases qLoop with ⟨⟨gq, hgqF⟩, hgqloop⟩
          have hqold :=
            suppressPair_expanded_loop_left_nonloop_old
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) he hf hxv hyv hgqF hgqloop
          dsimp [suppressPair_expanded_degreeTokenTo_left_nonloop] at hpq
          rw [dif_pos hpold, dif_pos hqold] at hpq
          injection hpq with hsub
          have hlabelStep :
              (Sum.inl gp : StepEdge E) = Sum.inl gq :=
            congrArg (fun z => z.1.1) hsub
          have hlabel : gp = gq := Sum.inl_injective hlabelStep
          subst gq
          simp

private lemma suppressPair_expanded_degreeToken_card_eq_left_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    Nat.card (DegreeTokenInEdgeSet G
      (expandedEdgeSupport (E := E) C.edgeSupport e f) x) =
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
        C.edgeSupport x) := by
  classical
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  haveI : Finite (expandedEdgeSupport (E := E) C.edgeSupport e f) :=
    Set.Finite.to_subtype
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f)
  have hle₁ :
      Nat.card (DegreeTokenInEdgeSet G
        (expandedEdgeSupport (E := E) C.edgeSupport e f) x) ≤
        Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
          C.edgeSupport x) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenTo_left_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C hnew he hf hxv hyv hxy)
      (suppressPair_expanded_degreeTokenTo_left_nonloop_injective
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C hnew he hf hxv hyv hxy)
  have hle₂ :
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
        C.edgeSupport x) ≤
        Nat.card (DegreeTokenInEdgeSet G
          (expandedEdgeSupport (E := E) C.edgeSupport e f) x) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenFrom_left_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hxv hyv hxy)
      (suppressPair_expanded_degreeTokenFrom_left_nonloop_injective
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hxv hyv hxy)
  omega

private lemma suppressPair_expanded_diestelDegreeInEdgeSet_eq_left_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    G.diestelDegreeInEdgeSet
        (expandedEdgeSupport (E := E) C.edgeSupport e f) x =
      (suppressPair G v x y e f).diestelDegreeInEdgeSet
        C.edgeSupport x := by
  rw [diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := G)
      (F := expandedEdgeSupport (E := E) C.edgeSupport e f)
      (v := x)
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f),
    diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := suppressPair G v x y e f)
      (F := C.edgeSupport)
      (v := x)
      C.edgeSupport_finite]
  exact suppressPair_expanded_degreeToken_card_eq_left_nonloop
    (G := G) (v := v) (x := x) (y := y)
    (e := e) (f := f) C hnew he hf hxv hyv hxy

private noncomputable def suppressPair_expanded_degreeTokenTo_right_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) y →
      DegreeTokenInEdgeSet (suppressPair G v x y e f) C.edgeSupport y := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgF⟩, hginc⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inl ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_inc_of_original_inc_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            heH hginc⟩
      else if hge : g = e then
        subst g
        have hfalse : False :=
          suppressPair_not_inc_right_of_left_edge (G := G) he hyv (Ne.symm hxy)
            ⟨he.edge_mem, hginc⟩
        exact False.elim hfalse
      else if hgf : g = f then
        subst g
        exact Sum.inl ⟨⟨Sum.inr (), hnew⟩,
          (suppressPair_new_inc_of_eq_right (G := G)
            (v := v) (x := x) (y := y) (a := y)
            (e := e) (f := f) rfl he.right_mem hf.right_mem hxv hyv).2⟩
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgF⟩, hgloop⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inr ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_loopAt_of_original_loopAt_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
            heH hgloop⟩
      else if hge : g = e then
        subst g
        exact False.elim
          (not_loopAt_of_isLink_ne (G := G) he hxv hgloop)
      else if hgf : g = f then
        subst g
        exact False.elim (suppressPair_right_edge_not_loop_at_right (G := G) hf hyv
          ⟨hf.edge_mem, hgloop⟩)
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse

private noncomputable def suppressPair_expanded_degreeTokenFrom_right_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    DegreeTokenInEdgeSet (suppressPair G v x y e f) C.edgeSupport y →
      DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) y := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgC⟩, hginc⟩
      cases g with
      | inl old =>
          exact Sum.inl ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            (original_incident_of_suppressPair_old_incident
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f)
              ⟨hginc.edge_mem, hginc⟩).2⟩
      | inr u =>
          exact Sum.inl ⟨⟨f, by simp [expandedEdgeSupport]⟩, hf.inc_right⟩
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgC⟩, hgloop⟩
      cases g with
      | inl old =>
          have hloopG : G.IsLoopAt old y :=
            original_isLink_of_suppressPair_old_isLink (G := G) hgloop
          exact Sum.inr ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            hloopG⟩
      | inr u =>
          have hnew :=
            (suppressPair_new_loopAt_iff (G := G) (v := v)
              (x := x) (y := y) (a := y) (e := e) (f := f)).mp hgloop
          exact False.elim (hxy hnew.1.symm)

private lemma suppressPair_expanded_inc_right_nonloop_old_or_right
    {G : MultiGraph V E} {v x y : V} {e f g : E}
    {C : (suppressPair G v x y e f).DiestelCycleIn}
    (he : G.IsLink e v x) (hyv : y ≠ v) (hxy : x ≠ y)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hginc : G.Inc g y) :
    Sum.inl g ∈ C.edgeSupport ∨ g = f := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact Or.inl hold
  · subst g
    exact (suppressPair_not_inc_right_of_left_edge (G := G) he hyv
      (Ne.symm hxy) ⟨he.edge_mem, hginc⟩).elim
  · exact Or.inr hgf

private lemma suppressPair_expanded_loop_right_nonloop_old
    {G : MultiGraph V E} {v x y : V} {e f g : E}
    {C : (suppressPair G v x y e f).DiestelCycleIn}
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hgloop : G.IsLoopAt g y) :
    Sum.inl g ∈ C.edgeSupport := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact hold
  · subst g
    exact (not_loopAt_of_isLink_ne (G := G) he hxv hgloop).elim
  · subst g
    exact (suppressPair_right_edge_not_loop_at_right (G := G) hf hyv
      ⟨hf.edge_mem, hgloop⟩).elim

private lemma suppressPair_expanded_degreeTokenFrom_right_nonloop_injective
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    Function.Injective
      (suppressPair_expanded_degreeTokenFrom_right_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hxv hyv hxy) := by
  classical
  intro p q hpq
  cases p with
  | inl pInc =>
      rcases pInc with ⟨⟨gp, hgpC⟩, hgpinc⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := y)
                    (e := e) (f := f) C hgpC).2
                  exact (hne hpq).elim
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := y) (e := e) (f := f)).mp hgqloop
                  exact (hxy hnew.1.symm).elim
      | inr u =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := y)
                    (e := e) (f := f) C hgqC).2
                  exact (hne hpq.symm).elim
              | inr u =>
                  simp
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := y) (e := e) (f := f)).mp hgqloop
                  exact (hxy hnew.1.symm).elim
  | inr pLoop =>
      rcases pLoop with ⟨⟨gp, hgpC⟩, hgploop⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_right_nonloop] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  have hnew :=
                    (suppressPair_new_loopAt_iff (G := G) (v := v)
                      (x := x) (y := y) (a := y) (e := e) (f := f)).mp hgqloop
                  exact (hxy hnew.1.symm).elim
      | inr u =>
          have hnew :=
            (suppressPair_new_loopAt_iff (G := G) (v := v)
              (x := x) (y := y) (a := y) (e := e) (f := f)).mp hgploop
          exact (hxy hnew.1.symm).elim

private lemma suppressPair_expanded_degreeTokenTo_right_nonloop_injective
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    Function.Injective
      (suppressPair_expanded_degreeTokenTo_right_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C hnew he hf hxv hyv hxy) := by
  classical
  have hnotOldF : Sum.inl f ∉ C.edgeSupport :=
    suppressPair_right_not_mem_oldEdgeSupport_of_cycle
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f) C
  have hfe : f ≠ e := by
    intro hfe
    subst f
    rcases he.right_eq_or_eq hf with hxv' | hxy'
    · exact hxv hxv'
    · exact hxy hxy'
  intro p q hpq
  cases p with
  | inl pInc =>
      rcases pInc with ⟨⟨gp, hgpF⟩, hgpinc⟩
      have hpclass :=
        suppressPair_expanded_inc_right_nonloop_old_or_right
          (G := G) (v := v) (x := x) (y := y)
          (e := e) (f := f) (C := C) he hyv hxy hgpF hgpinc
      cases q with
      | inl qInc =>
          rcases qInc with ⟨⟨gq, hgqF⟩, hgqinc⟩
          have hqclass :=
            suppressPair_expanded_inc_right_nonloop_old_or_right
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) he hyv hxy hgqF hgqinc
          rcases hpclass with hpold | hpf
          · rcases hqclass with hqold | hqf
            · dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
              rw [dif_pos hpold, dif_pos hqold] at hpq
              injection hpq with hsub
              have hlabelStep :
                  (Sum.inl gp : StepEdge E) = Sum.inl gq :=
                congrArg (fun z => z.1.1) hsub
              have hlabel : gp = gq := Sum.inl_injective hlabelStep
              subst gq
              simp
            · subst gq
              dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
              rw [dif_pos hpold, dif_neg hnotOldF, dif_neg hfe, dif_pos rfl] at hpq
              · simp at hpq
          · subst gp
            rcases hqclass with hqold | hqf
            · dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
              rw [dif_neg hnotOldF, dif_neg hfe, dif_pos rfl, dif_pos hqold] at hpq
              · simp at hpq
            · subst gq
              simp
      | inr qLoop =>
          rcases qLoop with ⟨⟨gq, hgqF⟩, hgqloop⟩
          have hqold :=
            suppressPair_expanded_loop_right_nonloop_old
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) he hf hxv hyv hgqF hgqloop
          rcases hpclass with hpold | hpf
          · dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
            rw [dif_pos hpold, dif_pos hqold] at hpq
            simp at hpq
          · subst gp
            dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
            rw [dif_neg hnotOldF, dif_neg hfe, dif_pos rfl, dif_pos hqold] at hpq
            · simp at hpq
  | inr pLoop =>
      rcases pLoop with ⟨⟨gp, hgpF⟩, hgploop⟩
      have hpold :=
        suppressPair_expanded_loop_right_nonloop_old
          (G := G) (v := v) (x := x) (y := y)
          (e := e) (f := f) (C := C) he hf hxv hyv hgpF hgploop
      cases q with
      | inl qInc =>
          rcases qInc with ⟨⟨gq, hgqF⟩, hgqinc⟩
          have hqclass :=
            suppressPair_expanded_inc_right_nonloop_old_or_right
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) he hyv hxy hgqF hgqinc
          rcases hqclass with hqold | hqf
          · dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
            rw [dif_pos hpold, dif_pos hqold] at hpq
            simp at hpq
          · subst gq
            dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
            rw [dif_pos hpold, dif_neg hnotOldF, dif_neg hfe, dif_pos rfl] at hpq
            · simp at hpq
      | inr qLoop =>
          rcases qLoop with ⟨⟨gq, hgqF⟩, hgqloop⟩
          have hqold :=
            suppressPair_expanded_loop_right_nonloop_old
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) (C := C) he hf hxv hyv hgqF hgqloop
          dsimp [suppressPair_expanded_degreeTokenTo_right_nonloop] at hpq
          rw [dif_pos hpold, dif_pos hqold] at hpq
          injection hpq with hsub
          have hlabelStep :
              (Sum.inl gp : StepEdge E) = Sum.inl gq :=
            congrArg (fun z => z.1.1) hsub
          have hlabel : gp = gq := Sum.inl_injective hlabelStep
          subst gq
          simp

private lemma suppressPair_expanded_degreeToken_card_eq_right_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    Nat.card (DegreeTokenInEdgeSet G
      (expandedEdgeSupport (E := E) C.edgeSupport e f) y) =
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
        C.edgeSupport y) := by
  classical
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  haveI : Finite (expandedEdgeSupport (E := E) C.edgeSupport e f) :=
    Set.Finite.to_subtype
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f)
  have hle₁ :
      Nat.card (DegreeTokenInEdgeSet G
        (expandedEdgeSupport (E := E) C.edgeSupport e f) y) ≤
        Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
          C.edgeSupport y) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenTo_right_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C hnew he hf hxv hyv hxy)
      (suppressPair_expanded_degreeTokenTo_right_nonloop_injective
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C hnew he hf hxv hyv hxy)
  have hle₂ :
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x y e f)
        C.edgeSupport y) ≤
        Nat.card (DegreeTokenInEdgeSet G
          (expandedEdgeSupport (E := E) C.edgeSupport e f) y) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenFrom_right_nonloop
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hxv hyv hxy)
      (suppressPair_expanded_degreeTokenFrom_right_nonloop_injective
        (G := G) (v := v) (x := x) (y := y)
        (e := e) (f := f) C he hf hxv hyv hxy)
  omega

private lemma suppressPair_expanded_diestelDegreeInEdgeSet_eq_right_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    G.diestelDegreeInEdgeSet
        (expandedEdgeSupport (E := E) C.edgeSupport e f) y =
      (suppressPair G v x y e f).diestelDegreeInEdgeSet
        C.edgeSupport y := by
  rw [diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := G)
      (F := expandedEdgeSupport (E := E) C.edgeSupport e f)
      (v := y)
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f),
    diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := suppressPair G v x y e f)
      (F := C.edgeSupport)
      (v := y)
      C.edgeSupport_finite]
  exact suppressPair_expanded_degreeToken_card_eq_right_nonloop
    (G := G) (v := v) (x := x) (y := y)
    (e := e) (f := f) C hnew he hf hxv hyv hxy

private noncomputable def suppressPair_expanded_degreeTokenTo_loop_endpoint
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) x →
      DegreeTokenInEdgeSet (suppressPair G v x x e f) C.edgeSupport x := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgF⟩, hginc⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x x e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inl ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_inc_of_original_inc_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
            heH hginc⟩
      else if hge : g = e then
        subst g
        exact Sum.inl ⟨⟨Sum.inr (), hnew⟩,
          (suppressPair_new_inc_of_eq_left (G := G)
            (v := v) (x := x) (y := x) (a := x)
            (e := e) (f := f) rfl he.right_mem hf.right_mem hxv hxv).2⟩
      else if hgf : g = f then
        subst g
        exact Sum.inr ⟨⟨Sum.inr (), hnew⟩,
          (suppressPair_new_loop_incident (G := G)
            (v := v) (x := x) (y := x) (a := x)
            (e := e) (f := f) rfl rfl he.right_mem hf.right_mem hxv hxv).2⟩
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgF⟩, hgloop⟩
      if hold : Sum.inl g ∈ C.edgeSupport then
        have heH : Sum.inl g ∈ (suppressPair G v x x e f).edgeSet :=
          (C.edges_inside hold).1
        exact Sum.inr ⟨⟨Sum.inl g, hold⟩,
          suppressPair_old_loopAt_of_original_loopAt_of_old_edge_mem
            (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
            heH hgloop⟩
      else if hge : g = e then
        subst g
        exact False.elim
          (not_loopAt_of_isLink_ne (G := G) he hxv hgloop)
      else if hgf : g = f then
        subst g
        exact False.elim
          (not_loopAt_of_isLink_ne (G := G) hf hxv hgloop)
      else
        have hfalse : False := by
          rcases (mem_expandedEdgeSupport.mp hgF) with hold' | hge' | hgf'
          · exact hold hold'
          · exact hge hge'
          · exact hgf hgf'
        exact False.elim hfalse

private noncomputable def suppressPair_expanded_degreeTokenFrom_loop_endpoint
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    DegreeTokenInEdgeSet (suppressPair G v x x e f) C.edgeSupport x →
      DegreeTokenInEdgeSet G (expandedEdgeSupport (E := E) C.edgeSupport e f) x := by
  classical
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgC⟩, hginc⟩
      cases g with
      | inl old =>
          exact Sum.inl ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            (original_incident_of_suppressPair_old_incident
              (G := G) (v := v) (x := x) (y := x)
              (e := e) (f := f)
              ⟨hginc.edge_mem, hginc⟩).2⟩
      | inr u =>
          exact Sum.inl ⟨⟨e, by simp [expandedEdgeSupport]⟩, he.inc_right⟩
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgC⟩, hgloop⟩
      cases g with
      | inl old =>
          have hloopG : G.IsLoopAt old x :=
            original_isLink_of_suppressPair_old_isLink (G := G) hgloop
          exact Sum.inr ⟨⟨old, by simp [expandedEdgeSupport, oldEdgeSupport, hgC]⟩,
            hloopG⟩
      | inr u =>
          exact Sum.inl ⟨⟨f, by simp [expandedEdgeSupport]⟩, hf.inc_right⟩

private lemma suppressPair_expanded_inc_loop_endpoint_old_or_left_or_right
    {G : MultiGraph V E} {v x : V} {e f g : E}
    {C : (suppressPair G v x x e f).DiestelCycleIn}
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f) :
    Sum.inl g ∈ C.edgeSupport ∨ g = e ∨ g = f := by
  simpa using (mem_expandedEdgeSupport.mp hgF)

private lemma suppressPair_expanded_loop_loop_endpoint_old
    {G : MultiGraph V E} {v x : V} {e f g : E}
    {C : (suppressPair G v x x e f).DiestelCycleIn}
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v)
    (hgF : g ∈ expandedEdgeSupport (E := E) C.edgeSupport e f)
    (hgloop : G.IsLoopAt g x) :
    Sum.inl g ∈ C.edgeSupport := by
  rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
  · exact hold
  · subst g
    exact (not_loopAt_of_isLink_ne (G := G) he hxv hgloop).elim
  · subst g
    exact (not_loopAt_of_isLink_ne (G := G) hf hxv hgloop).elim

private lemma suppressPair_expanded_degreeTokenFrom_loop_endpoint_injective
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    Function.Injective
      (suppressPair_expanded_degreeTokenFrom_loop_endpoint
        (G := G) (v := v) (x := x)
        (e := e) (f := f) C he hf hxv) := by
  classical
  intro p q hpq
  cases p with
  | inl pInc =>
      rcases pInc with ⟨⟨gp, hgpC⟩, hgpinc⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := x)
                    (e := e) (f := f) C hgpC).1
                  exact (hne hpq).elim
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := x)
                    (e := e) (f := f) C hgpC).2
                  exact (hne hpq).elim
      | inr u =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := x)
                    (e := e) (f := f) C hgqC).1
                  exact (hne hpq.symm).elim
              | inr u =>
                  simp
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp [hef] at hpq
  | inr pLoop =>
      rcases pLoop with ⟨⟨gp, hgpC⟩, hgploop⟩
      cases gp with
      | inl oldp =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
                  subst oldq
                  simp
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
      | inr u =>
          cases q with
          | inl qInc =>
              rcases qInc with ⟨⟨gq, hgqC⟩, hgqinc⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
                  have hne := (suppressPair_old_edge_ne_left_right_of_cycle_mem
                    (G := G) (v := v) (x := x) (y := x)
                    (e := e) (f := f) C hgqC).2
                  exact (hne hpq.symm).elim
              | inr u =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp [hef] at hpq
                  exact (hef hpq.symm).elim
          | inr qLoop =>
              rcases qLoop with ⟨⟨gq, hgqC⟩, hgqloop⟩
              cases gq with
              | inl oldq =>
                  dsimp [suppressPair_expanded_degreeTokenFrom_loop_endpoint] at hpq
                  simp at hpq
              | inr u =>
                  simp

private lemma suppressPair_expanded_degreeTokenFromTo_loop_endpoint
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    ∀ t : DegreeTokenInEdgeSet G
        (expandedEdgeSupport (E := E) C.edgeSupport e f) x,
      suppressPair_expanded_degreeTokenFrom_loop_endpoint
          (G := G) (v := v) (x := x)
          (e := e) (f := f) C he hf hxv
        (suppressPair_expanded_degreeTokenTo_loop_endpoint
          (G := G) (v := v) (x := x)
          (e := e) (f := f) C hnew he hf hxv t) = t := by
  classical
  have hnotOldE : Sum.inl e ∉ C.edgeSupport :=
    suppressPair_left_not_mem_oldEdgeSupport_of_cycle
      (G := G) (v := v) (x := x) (y := x) (e := e) (f := f) C
  have hnotOldF : Sum.inl f ∉ C.edgeSupport :=
    suppressPair_right_not_mem_oldEdgeSupport_of_cycle
      (G := G) (v := v) (x := x) (y := x) (e := e) (f := f) C
  have hfe : f ≠ e := hef.symm
  intro t
  cases t with
  | inl incTok =>
      rcases incTok with ⟨⟨g, hgF⟩, hginc⟩
      rcases suppressPair_expanded_inc_loop_endpoint_old_or_left_or_right
          (G := G) (v := v) (x := x) (e := e) (f := f)
          (C := C) hgF with hold | hge | hgf
      · dsimp [suppressPair_expanded_degreeTokenTo_loop_endpoint,
          suppressPair_expanded_degreeTokenFrom_loop_endpoint]
        rw [dif_pos hold]
      · subst g
        dsimp [suppressPair_expanded_degreeTokenTo_loop_endpoint,
          suppressPair_expanded_degreeTokenFrom_loop_endpoint]
        rw [dif_neg hnotOldE, dif_pos rfl]
      · subst g
        dsimp [suppressPair_expanded_degreeTokenTo_loop_endpoint,
          suppressPair_expanded_degreeTokenFrom_loop_endpoint]
        rw [dif_neg hnotOldF, dif_neg hfe, dif_pos rfl]
  | inr loopTok =>
      rcases loopTok with ⟨⟨g, hgF⟩, hgloop⟩
      have hold :
          Sum.inl g ∈ C.edgeSupport :=
        suppressPair_expanded_loop_loop_endpoint_old
          (G := G) (v := v) (x := x) (e := e) (f := f)
          (C := C) he hf hxv hgF hgloop
      dsimp [suppressPair_expanded_degreeTokenTo_loop_endpoint,
        suppressPair_expanded_degreeTokenFrom_loop_endpoint]
      rw [dif_pos hold]

private lemma suppressPair_expanded_degreeTokenTo_loop_endpoint_injective
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    Function.Injective
      (suppressPair_expanded_degreeTokenTo_loop_endpoint
        (G := G) (v := v) (x := x)
        (e := e) (f := f) C hnew he hf hxv) := by
  intro p q hpq
  have hleft :=
    suppressPair_expanded_degreeTokenFromTo_loop_endpoint
      (G := G) (v := v) (x := x) (e := e) (f := f)
      C hnew hef he hf hxv
  calc
    p =
        suppressPair_expanded_degreeTokenFrom_loop_endpoint
          (G := G) (v := v) (x := x)
          (e := e) (f := f) C he hf hxv
          (suppressPair_expanded_degreeTokenTo_loop_endpoint
            (G := G) (v := v) (x := x)
            (e := e) (f := f) C hnew he hf hxv p) := (hleft p).symm
    _ =
        suppressPair_expanded_degreeTokenFrom_loop_endpoint
          (G := G) (v := v) (x := x)
          (e := e) (f := f) C he hf hxv
          (suppressPair_expanded_degreeTokenTo_loop_endpoint
            (G := G) (v := v) (x := x)
            (e := e) (f := f) C hnew he hf hxv q) := by rw [hpq]
    _ = q := hleft q

private lemma suppressPair_expanded_degreeToken_card_eq_loop_endpoint
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    Nat.card (DegreeTokenInEdgeSet G
      (expandedEdgeSupport (E := E) C.edgeSupport e f) x) =
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x x e f)
        C.edgeSupport x) := by
  classical
  haveI : Finite C.edgeSupport := Set.Finite.to_subtype C.edgeSupport_finite
  haveI : Finite (expandedEdgeSupport (E := E) C.edgeSupport e f) :=
    Set.Finite.to_subtype
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f)
  have hle₁ :
      Nat.card (DegreeTokenInEdgeSet G
        (expandedEdgeSupport (E := E) C.edgeSupport e f) x) ≤
        Nat.card (DegreeTokenInEdgeSet (suppressPair G v x x e f)
          C.edgeSupport x) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenTo_loop_endpoint
        (G := G) (v := v) (x := x)
        (e := e) (f := f) C hnew he hf hxv)
      (suppressPair_expanded_degreeTokenTo_loop_endpoint_injective
        (G := G) (v := v) (x := x)
        (e := e) (f := f) C hnew hef he hf hxv)
  have hle₂ :
      Nat.card (DegreeTokenInEdgeSet (suppressPair G v x x e f)
        C.edgeSupport x) ≤
        Nat.card (DegreeTokenInEdgeSet G
          (expandedEdgeSupport (E := E) C.edgeSupport e f) x) :=
    Nat.card_le_card_of_injective
      (suppressPair_expanded_degreeTokenFrom_loop_endpoint
        (G := G) (v := v) (x := x)
        (e := e) (f := f) C he hf hxv)
      (suppressPair_expanded_degreeTokenFrom_loop_endpoint_injective
        (G := G) (v := v) (x := x)
        (e := e) (f := f) C hef he hf hxv)
  omega

private lemma suppressPair_expanded_diestelDegreeInEdgeSet_eq_loop_endpoint
    {G : MultiGraph V E} {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hxv : x ≠ v) :
    G.diestelDegreeInEdgeSet
        (expandedEdgeSupport (E := E) C.edgeSupport e f) x =
      (suppressPair G v x x e f).diestelDegreeInEdgeSet
        C.edgeSupport x := by
  rw [diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := G)
      (F := expandedEdgeSupport (E := E) C.edgeSupport e f)
      (v := x)
      (expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f),
    diestelDegreeInEdgeSet_eq_card_degreeTokenInEdgeSet
      (G := suppressPair G v x x e f)
      (F := C.edgeSupport)
      (v := x)
      C.edgeSupport_finite]
  exact suppressPair_expanded_degreeToken_card_eq_loop_endpoint
    (G := G) (v := v) (x := x)
    (e := e) (f := f) C hnew hef he hf hxv

def diestelCycleIn_of_suppressPair_avoids_new {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hNoNew : Sum.inr () ∉ C.edgeSupport) : G.DiestelCycleIn where
  support := C.support
  edgeSupport := oldEdgeSupport (E := E) C.edgeSupport
  edgeSupport_finite := oldEdgeSupport_finite (E := E) C.edgeSupport_finite
  edges_inside := by
    intro old hold
    have holdC : Sum.inl old ∈ C.edgeSupport := by
      simpa using hold
    have heH : Sum.inl old ∈ (suppressPair G v x y e f).edgeSet :=
      (C.edges_inside holdC).1
    refine ⟨original_edge_mem_of_suppressPair_old_edge_mem
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f) heH, ?_⟩
    intro a hinc
    exact (C.edges_inside holdC).2 a
      (suppressPair_old_inc_of_original_inc_of_old_edge_mem
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        heH hinc)
  support_nonempty := C.support_nonempty
  connected := by
    rcases C.connected with ⟨hpre⟩
    refine ⟨?_⟩
    intro a b
    exact (hpre a b).mono fun p q hpq => by
      rcases hpq with ⟨hne, g, hgC, hgH, hlinkH⟩
      cases g with
      | inl old =>
          exact ⟨hne, old, by simpa using hgC,
            original_edge_mem_of_suppressPair_old_edge_mem
              (G := G) (v := v) (x := x) (y := y)
              (e := e) (f := f) hgH,
            original_isLink_of_suppressPair_old_isLink (G := G) hlinkH⟩
      | inr u =>
          exact False.elim (hNoNew (by simpa using hgC))
  degree_two := by
    intro a ha
    change
      Nat.card {g : oldEdgeSupport (E := E) C.edgeSupport // G.Inc g.1 a} +
          Nat.card {g : oldEdgeSupport (E := E) C.edgeSupport // G.IsLoopAt g.1 a} = 2
    rw [Nat.card_congr (oldEdgeSupport_incEquiv
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C hNoNew),
      Nat.card_congr (oldEdgeSupport_loopEquiv
        (G := G) (v := v) (x := x) (y := y) (a := a)
        (e := e) (f := f) C hNoNew)]
    exact C.degree_two a ha

lemma diestelCycleIn_of_suppressPair_avoids_new_support {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hNoNew : Sum.inr () ∉ C.edgeSupport) :
    (diestelCycleIn_of_suppressPair_avoids_new
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      C hNoNew).support = C.support := rfl

lemma hasKDisjointDiestelCycles_of_suppressPair_all_avoid_new {G : MultiGraph V E}
    {v x y : V} {e f : E} {k : ℕ}
    (C : Fin k → (suppressPair G v x y e f).DiestelCycleIn)
    (hdisj : Pairwise fun i j => Disjoint (C i).support (C j).support)
    (hNoNew : ∀ i : Fin k, Sum.inr () ∉ (C i).edgeSupport) :
    G.HasKDisjointDiestelCycles k := by
  classical
  refine ⟨fun i =>
    diestelCycleIn_of_suppressPair_avoids_new
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      (C i) ?_, ?_⟩
  · simpa using hNoNew i
  · intro i j hij
    simpa [diestelCycleIn_of_suppressPair_avoids_new_support] using hdisj hij

lemma suppressPair_new_edge_endpoint_mem_support {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport) :
    x ∈ C.support ∧ y ∈ C.support := by
  classical
  have heInside := C.edges_inside hnew
  obtain ⟨a, b, hlink⟩ :=
    Graph.exists_isLink_of_mem_edgeSet
      (G := suppressPair G v x y e f) heInside.1
  have hvalid :
      x ∈ G.vertexSet ∧ y ∈ G.vertexSet ∧ x ≠ v ∧ y ≠ v := hlink.2
  have hxinc :
      (suppressPair G v x y e f).Inc (Sum.inr ()) x := by
    rw [suppressPair_new_inc_iff]
    exact ⟨Or.inl rfl, hvalid⟩
  have hyinc :
      (suppressPair G v x y e f).Inc (Sum.inr ()) y := by
    rw [suppressPair_new_inc_iff]
    exact ⟨Or.inr rfl, hvalid⟩
  exact ⟨heInside.2 x hxinc, heInside.2 y hyinc⟩

private lemma suppressPair_expanded_cycle_connected {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    ((G.edgeSubgraph (expandedEdgeSupport (E := E) C.edgeSupport e f)).induce
      (expandedSupport C.support v)).Connected := by
  classical
  let T : SimpleGraph (expandedSupport C.support v) :=
    (G.edgeSubgraph (expandedEdgeSupport (E := E) C.edgeSupport e f)).induce
      (expandedSupport C.support v)
  have hxC : x ∈ C.support :=
    (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
      (x := x) (y := y) (e := e) (f := f) C hnew).1
  have hyC : y ∈ C.support :=
    (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
      (x := x) (y := y) (e := e) (f := f) C hnew).2
  let xT : expandedSupport C.support v := ⟨x, by simp [expandedSupport, hxC]⟩
  let yT : expandedSupport C.support v := ⟨y, by simp [expandedSupport, hyC]⟩
  let vT : expandedSupport C.support v := ⟨v, by simp [expandedSupport]⟩
  have hAdj_xv : T.Adj xT vT := by
    change (G.edgeSubgraph (expandedEdgeSupport (E := E) C.edgeSupport e f)).Adj x v
    refine ⟨hxv, e, ?_, he.edge_mem, he.symm⟩
    simp [expandedEdgeSupport]
  have hAdj_vy : T.Adj vT yT := by
    change (G.edgeSubgraph (expandedEdgeSupport (E := E) C.edgeSupport e f)).Adj v y
    refine ⟨(fun h => hyv h.symm), f, ?_, hf.edge_mem, hf⟩
    simp [expandedEdgeSupport]
  have hReach_xy : T.Reachable xT yT :=
    hAdj_xv.reachable.trans hAdj_vy.reachable
  have hmap :
      ∀ a b : C.support,
        (((suppressPair G v x y e f).edgeSubgraph C.edgeSupport).induce C.support).Adj a b →
          T.Reachable
            (⟨a.1, by simp [expandedSupport, a.2]⟩ : expandedSupport C.support v)
            (⟨b.1, by simp [expandedSupport, b.2]⟩ : expandedSupport C.support v) := by
    intro a b hadj
    rcases hadj with ⟨hne, g, hgC, hgH, hlinkH⟩
    cases g with
    | inl old =>
        have hadjT :
            T.Adj
              (⟨a.1, by simp [expandedSupport, a.2]⟩ : expandedSupport C.support v)
              (⟨b.1, by simp [expandedSupport, b.2]⟩ : expandedSupport C.support v) := by
          change
            (G.edgeSubgraph (expandedEdgeSupport (E := E) C.edgeSupport e f)).Adj
              (a : V) (b : V)
          refine ⟨hne, old, ?_, ?_, ?_⟩
          · simp [expandedEdgeSupport, oldEdgeSupport, hgC]
          · exact original_edge_mem_of_suppressPair_old_edge_mem
              (G := G) (v := v) (x := x) (y := y) (e := e) (f := f) hgH
          · exact original_isLink_of_suppressPair_old_isLink (G := G) hlinkH
        exact hadjT.reachable
    | inr u =>
        rcases hlinkH.1 with hxy | hyx
        · have ha : (⟨a.1, by simp [expandedSupport, a.2]⟩ :
              expandedSupport C.support v) = xT := by
            ext
            exact hxy.1
          have hb : (⟨b.1, by simp [expandedSupport, b.2]⟩ :
              expandedSupport C.support v) = yT := by
            ext
            exact hxy.2
          simpa [ha, hb] using hReach_xy
        · have ha : (⟨a.1, by simp [expandedSupport, a.2]⟩ :
              expandedSupport C.support v) = yT := by
            ext
            exact hyx.1
          have hb : (⟨b.1, by simp [expandedSupport, b.2]⟩ :
              expandedSupport C.support v) = xT := by
            ext
            exact hyx.2
          simpa [ha, hb] using hReach_xy.symm
  have hReachInC :
      ∀ a b : C.support,
        T.Reachable
          (⟨a.1, by simp [expandedSupport, a.2]⟩ : expandedSupport C.support v)
          (⟨b.1, by simp [expandedSupport, b.2]⟩ : expandedSupport C.support v) := by
    intro a b
    exact reachable_map_of_adj_reachable
      (φ := fun z : C.support =>
        (⟨z.1, by simp [expandedSupport, z.2]⟩ : expandedSupport C.support v))
      hmap (C.connected a b)
  haveI : Nonempty (expandedSupport C.support v) := ⟨xT⟩
  refine ⟨?_⟩
  intro a b
  have hToX : ∀ z : expandedSupport C.support v, T.Reachable z xT := by
    intro z
    rcases z with ⟨z, hz⟩
    rcases (mem_expandedSupport.mp hz) with hzC | rfl
    · simpa [xT] using hReachInC ⟨z, hzC⟩ ⟨x, hxC⟩
    · simpa [xT, vT] using hAdj_xv.symm.reachable
  exact (hToX a).trans (hToX b).symm

def diestelCycleIn_of_suppressPair_uses_new_nonloop {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    G.DiestelCycleIn where
  support := expandedSupport C.support v
  edgeSupport := expandedEdgeSupport (E := E) C.edgeSupport e f
  edgeSupport_finite := expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f
  edges_inside := by
    intro g hgF
    refine ⟨original_edge_mem_of_mem_expandedEdgeSupport
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      C he hf hgF, ?_⟩
    intro a hinc
    rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
    · have heH : Sum.inl g ∈ (suppressPair G v x y e f).edgeSet :=
        (C.edges_inside hold).1
      have hHinc :
          (suppressPair G v x y e f).Inc (Sum.inl g) a :=
        suppressPair_old_inc_of_original_inc_of_old_edge_mem
          (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
          heH hinc
      exact Or.inl ((C.edges_inside hold).2 a hHinc)
    · subst g
      rcases hinc.eq_or_eq_of_isLink he with hav | hax
      · exact Or.inr hav
      · exact Or.inl
          (by
            have hxC :=
              (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
                (x := x) (y := y) (e := e) (f := f) C hnew).1
            simpa [hax] using hxC)
    · subst g
      rcases hinc.eq_or_eq_of_isLink hf with hav | hay
      · exact Or.inr hav
      · exact Or.inl
          (by
            have hyC :=
              (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
                (x := x) (y := y) (e := e) (f := f) C hnew).2
            simpa [hay] using hyC)
  support_nonempty := ⟨v, by simp [expandedSupport]⟩
  connected :=
    suppressPair_expanded_cycle_connected
      (G := G) (v := v) (x := x) (y := y)
      (e := e) (f := f) C hnew he hf hxv hyv
  degree_two := by
    intro a ha
    rcases (mem_expandedSupport.mp ha) with haC | hav_eq
    · have haH :
          a ∈ (suppressPair G v x y e f).vertexSet :=
        diestelCycle_support_subset_vertexSet
          (G := suppressPair G v x y e f) C haC
      have hav : a ≠ v := by
        intro hav
        exact (suppressPair_removed_not_mem_vertexSet G v x y e f)
          (by simpa [hav] using haH)
      by_cases hax : a = x
      · subst a
        rw [suppressPair_expanded_diestelDegreeInEdgeSet_eq_left_nonloop
          (G := G) (v := v) (x := x) (y := y)
          (e := e) (f := f) C hnew he hf hxv hyv hxy]
        exact C.degree_two x
          ((suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
            (x := x) (y := y) (e := e) (f := f) C hnew).1)
      · by_cases hay : a = y
        · subst a
          rw [suppressPair_expanded_diestelDegreeInEdgeSet_eq_right_nonloop
            (G := G) (v := v) (x := x) (y := y)
            (e := e) (f := f) C hnew he hf hxv hyv hxy]
          exact C.degree_two y
            ((suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
              (x := x) (y := y) (e := e) (f := f) C hnew).2)
        · rw [suppressPair_expanded_diestelDegreeInEdgeSet_eq_of_not_endpoint
            (G := G) (v := v) (x := x) (y := y) (a := a)
            (e := e) (f := f) C he hf hxv hyv hav hax hay]
          exact C.degree_two a haC
    · simpa [hav_eq] using
        suppressPair_expanded_diestelDegreeInEdgeSet_suppressed_vertex
          (G := G) (v := v) (x := x) (y := y)
          (e := e) (f := f) C hef he hf hvef hxv hyv

def diestelCycleIn_of_suppressPair_uses_new_loop {G : MultiGraph V E}
    {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) :
    G.DiestelCycleIn where
  support := expandedSupport C.support v
  edgeSupport := expandedEdgeSupport (E := E) C.edgeSupport e f
  edgeSupport_finite := expandedEdgeSupport_finite (E := E) C.edgeSupport_finite e f
  edges_inside := by
    intro g hgF
    refine ⟨original_edge_mem_of_mem_expandedEdgeSupport
      (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
      C he hf hgF, ?_⟩
    intro a hinc
    rcases (mem_expandedEdgeSupport.mp hgF) with hold | hge | hgf
    · have heH : Sum.inl g ∈ (suppressPair G v x x e f).edgeSet :=
        (C.edges_inside hold).1
      have hHinc :
          (suppressPair G v x x e f).Inc (Sum.inl g) a :=
        suppressPair_old_inc_of_original_inc_of_old_edge_mem
          (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
          heH hinc
      exact Or.inl ((C.edges_inside hold).2 a hHinc)
    · subst g
      rcases hinc.eq_or_eq_of_isLink he with hav | hax
      · exact Or.inr hav
      · exact Or.inl
          (by
            have hxC :=
              (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
                (x := x) (y := x) (e := e) (f := f) C hnew).1
            simpa [hax] using hxC)
    · subst g
      rcases hinc.eq_or_eq_of_isLink hf with hav | hax
      · exact Or.inr hav
      · exact Or.inl
          (by
            have hxC :=
              (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
                (x := x) (y := x) (e := e) (f := f) C hnew).1
            simpa [hax] using hxC)
  support_nonempty := ⟨v, by simp [expandedSupport]⟩
  connected :=
    suppressPair_expanded_cycle_connected
      (G := G) (v := v) (x := x) (y := x)
      (e := e) (f := f) C hnew he hf hxv hxv
  degree_two := by
    intro a ha
    rcases (mem_expandedSupport.mp ha) with haC | hav_eq
    · have haH :
          a ∈ (suppressPair G v x x e f).vertexSet :=
        diestelCycle_support_subset_vertexSet
          (G := suppressPair G v x x e f) C haC
      have hav : a ≠ v := by
        intro hav
        exact (suppressPair_removed_not_mem_vertexSet G v x x e f)
          (by simpa [hav] using haH)
      by_cases hax : a = x
      · subst a
        rw [suppressPair_expanded_diestelDegreeInEdgeSet_eq_loop_endpoint
          (G := G) (v := v) (x := x)
          (e := e) (f := f) C hnew hef he hf hxv]
        exact C.degree_two x
          ((suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
            (x := x) (y := x) (e := e) (f := f) C hnew).1)
      · rw [suppressPair_expanded_diestelDegreeInEdgeSet_eq_of_not_endpoint
          (G := G) (v := v) (x := x) (y := x) (a := a)
          (e := e) (f := f) C he hf hxv hxv hav hax hax]
        exact C.degree_two a haC
    · simpa [hav_eq] using
        suppressPair_expanded_diestelDegreeInEdgeSet_suppressed_vertex
          (G := G) (v := v) (x := x) (y := x)
          (e := e) (f := f) C hef he hf hvef hxv hxv

lemma diestelCycleIn_of_suppressPair_uses_new_nonloop_support {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    (diestelCycleIn_of_suppressPair_uses_new_nonloop
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      C hnew hef he hf hvef hxv hyv hxy).support =
      expandedSupport C.support v := rfl

lemma diestelCycleIn_of_suppressPair_uses_new_loop_support {G : MultiGraph V E}
    {v x : V} {e f : E}
    (C : (suppressPair G v x x e f).DiestelCycleIn)
    (hnew : Sum.inr () ∈ C.edgeSupport)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) :
    (diestelCycleIn_of_suppressPair_uses_new_loop
      (G := G) (v := v) (x := x) (e := e) (f := f)
      C hnew hef he hf hvef hxv).support =
      expandedSupport C.support v := rfl

private lemma suppressPair_cycle_support_not_removed {G : MultiGraph V E}
    {v x y : V} {e f : E}
    (C : (suppressPair G v x y e f).DiestelCycleIn) :
    v ∉ C.support := by
  intro hvC
  exact (suppressPair_removed_not_mem_vertexSet G v x y e f)
    (diestelCycle_support_subset_vertexSet
      (G := suppressPair G v x y e f) C hvC)

private lemma disjoint_expandedSupport_left {S T : Set V} {v : V}
    (hST : Disjoint S T) (hvT : v ∉ T) :
    Disjoint (expandedSupport S v) T := by
  rw [Set.disjoint_left]
  intro a ha hT
  rcases (mem_expandedSupport.mp ha) with hS | rfl
  · exact (Set.disjoint_left.mp hST) hS hT
  · exact hvT hT

private lemma disjoint_expandedSupport_right {S T : Set V} {v : V}
    (hST : Disjoint S T) (hvS : v ∉ S) :
    Disjoint S (expandedSupport T v) := by
  rw [Set.disjoint_left]
  intro a hS ha
  rcases (mem_expandedSupport.mp ha) with hT | rfl
  · exact (Set.disjoint_left.mp hST) hS hT
  · exact hvS hS

private lemma suppressPair_new_edge_mem_unique_in_disjoint_cycles_aux
    {G : MultiGraph V E}
    {v x y : V} {e f : E} {k : ℕ}
    {C : Fin k → (suppressPair G v x y e f).DiestelCycleIn}
    (hdisj : Pairwise fun i j => Disjoint (C i).support (C j).support)
    {i j : Fin k} (hij : i ≠ j)
    (hi : Sum.inr () ∈ (C i).edgeSupport)
    (hj : Sum.inr () ∈ (C j).edgeSupport) :
    False := by
  have hxi : x ∈ (C i).support :=
    (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
      (x := x) (y := y) (e := e) (f := f) (C i) hi).1
  have hxj : x ∈ (C j).support :=
    (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
      (x := x) (y := y) (e := e) (f := f) (C j) hj).1
  exact (Set.disjoint_left.mp (hdisj hij)) hxi hxj

lemma hasKDisjointDiestelCycles_of_suppressPair_nonloop
    {G : MultiGraph V E} {v x y : V} {e f : E} {k : ℕ}
    (C : Fin k → (suppressPair G v x y e f).DiestelCycleIn)
    (hdisj : Pairwise fun i j => Disjoint (C i).support (C j).support)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) (hxy : x ≠ y) :
    G.HasKDisjointDiestelCycles k := by
  classical
  by_cases hAny : ∃ i : Fin k, Sum.inr () ∈ (C i).edgeSupport
  · rcases hAny with ⟨i0, hnew0⟩
    have hNoNew_of_ne :
        ∀ i : Fin k, i ≠ i0 → Sum.inr () ∉ (C i).edgeSupport := by
      intro i hi hnewi
      exact suppressPair_new_edge_mem_unique_in_disjoint_cycles_aux
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        hdisj hi hnewi hnew0
    let D : Fin k → G.DiestelCycleIn := fun i =>
      if hi : i = i0 then
        diestelCycleIn_of_suppressPair_uses_new_nonloop
          (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
          (C i) (by simpa [hi] using hnew0) hef he hf hvef hxv hyv hxy
      else
        diestelCycleIn_of_suppressPair_avoids_new
          (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
          (C i) (hNoNew_of_ne i hi)
    refine ⟨D, ?_⟩
    intro i j hij
    by_cases hi : i = i0
    · subst i
      by_cases hj : j = i0
      · exact (hij hj.symm).elim
      · have hbase : Disjoint (C i0).support (C j).support := hdisj hij
        have hvj : v ∉ (C j).support :=
          suppressPair_cycle_support_not_removed
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f) (C j)
        have hmain :
            Disjoint (expandedSupport (C i0).support v) (C j).support :=
          disjoint_expandedSupport_left hbase hvj
        simpa [D, hj,
          diestelCycleIn_of_suppressPair_uses_new_nonloop_support,
          diestelCycleIn_of_suppressPair_avoids_new_support] using hmain
    · by_cases hj : j = i0
      · subst j
        have hbase : Disjoint (C i).support (C i0).support := hdisj hij
        have hvi : v ∉ (C i).support :=
          suppressPair_cycle_support_not_removed
            (G := G) (v := v) (x := x) (y := y) (e := e) (f := f) (C i)
        have hmain :
            Disjoint (C i).support (expandedSupport (C i0).support v) :=
          disjoint_expandedSupport_right hbase hvi
        simpa [D, hi,
          diestelCycleIn_of_suppressPair_uses_new_nonloop_support,
          diestelCycleIn_of_suppressPair_avoids_new_support] using hmain
      · have hbase : Disjoint (C i).support (C j).support := hdisj hij
        simpa [D, hi, hj,
          diestelCycleIn_of_suppressPair_avoids_new_support] using hbase
  · exact hasKDisjointDiestelCycles_of_suppressPair_all_avoid_new
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      C hdisj (by
        intro i hnew
        exact hAny ⟨i, hnew⟩)

lemma hasKDisjointDiestelCycles_of_suppressPair_loop
    {G : MultiGraph V E} {v x : V} {e f : E} {k : ℕ}
    (C : Fin k → (suppressPair G v x x e f).DiestelCycleIn)
    (hdisj : Pairwise fun i j => Disjoint (C i).support (C j).support)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v x)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) :
    G.HasKDisjointDiestelCycles k := by
  classical
  by_cases hAny : ∃ i : Fin k, Sum.inr () ∈ (C i).edgeSupport
  · rcases hAny with ⟨i0, hnew0⟩
    have hNoNew_of_ne :
        ∀ i : Fin k, i ≠ i0 → Sum.inr () ∉ (C i).edgeSupport := by
      intro i hi hnewi
      exact suppressPair_new_edge_mem_unique_in_disjoint_cycles_aux
        (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
        hdisj hi hnewi hnew0
    let D : Fin k → G.DiestelCycleIn := fun i =>
      if hi : i = i0 then
        diestelCycleIn_of_suppressPair_uses_new_loop
          (G := G) (v := v) (x := x) (e := e) (f := f)
          (C i) (by simpa [hi] using hnew0) hef he hf hvef hxv
      else
        diestelCycleIn_of_suppressPair_avoids_new
          (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
          (C i) (hNoNew_of_ne i hi)
    refine ⟨D, ?_⟩
    intro i j hij
    by_cases hi : i = i0
    · subst i
      by_cases hj : j = i0
      · exact (hij hj.symm).elim
      · have hbase : Disjoint (C i0).support (C j).support := hdisj hij
        have hvj : v ∉ (C j).support :=
          suppressPair_cycle_support_not_removed
            (G := G) (v := v) (x := x) (y := x) (e := e) (f := f) (C j)
        have hmain :
            Disjoint (expandedSupport (C i0).support v) (C j).support :=
          disjoint_expandedSupport_left hbase hvj
        simpa [D, hj,
          diestelCycleIn_of_suppressPair_uses_new_loop_support,
          diestelCycleIn_of_suppressPair_avoids_new_support] using hmain
    · by_cases hj : j = i0
      · subst j
        have hbase : Disjoint (C i).support (C i0).support := hdisj hij
        have hvi : v ∉ (C i).support :=
          suppressPair_cycle_support_not_removed
            (G := G) (v := v) (x := x) (y := x) (e := e) (f := f) (C i)
        have hmain :
            Disjoint (C i).support (expandedSupport (C i0).support v) :=
          disjoint_expandedSupport_right hbase hvi
        simpa [D, hi,
          diestelCycleIn_of_suppressPair_uses_new_loop_support,
          diestelCycleIn_of_suppressPair_avoids_new_support] using hmain
      · have hbase : Disjoint (C i).support (C j).support := hdisj hij
        simpa [D, hi, hj,
          diestelCycleIn_of_suppressPair_avoids_new_support] using hbase
  · exact hasKDisjointDiestelCycles_of_suppressPair_all_avoid_new
      (G := G) (v := v) (x := x) (y := x) (e := e) (f := f)
      C hdisj (by
        intro i hnew
        exact hAny ⟨i, hnew⟩)

lemma hasKDisjointDiestelCycles_of_suppressPair
    {G : MultiGraph V E} {v x y : V} {e f : E} {k : ℕ}
    (C : Fin k → (suppressPair G v x y e f).DiestelCycleIn)
    (hdisj : Pairwise fun i j => Disjoint (C i).support (C j).support)
    (hef : e ≠ f)
    (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    G.HasKDisjointDiestelCycles k := by
  classical
  by_cases hxy : x = y
  · subst y
    exact hasKDisjointDiestelCycles_of_suppressPair_loop
      (G := G) (v := v) (x := x) (e := e) (f := f)
      C hdisj hef he hf hvef hxv
  · exact hasKDisjointDiestelCycles_of_suppressPair_nonloop
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      C hdisj hef he hf hvef hxv hyv hxy

private lemma suppressPair_diestelDegree_eq_of_mem_vertexSet {G : MultiGraph V E}
    [Finite E] {v x y a : V} {e f : E}
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (ha : a ∈ (suppressPair G v x y e f).vertexSet) :
    (suppressPair G v x y e f).diestelDegree a = G.diestelDegree a := by
  rw [suppressPair_vertexSet] at ha
  have hav : a ≠ v := by
    intro hav
    exact ha.2 (by simp [hav])
  by_cases hxy : x = y
  · subst y
    by_cases hax : a = x
    · subst a
      exact suppressPair_diestelDegree_eq_loop_endpoint
        (G := G) (v := v) (x := x) (e := e) (f := f)
        hef he hf hvef hxv
    · exact suppressPair_diestelDegree_eq_of_not_endpoint
        (G := G) (v := v) (x := x) (y := x) (a := a)
        (e := e) (f := f) he hf hvef hav hax hax
  · by_cases hax : a = x
    · subst a
      exact suppressPair_diestelDegree_eq_left_nonloop
        (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
        he hf hvef hxv hyv hxy
    · by_cases hay : a = y
      · subst a
        exact suppressPair_diestelDegree_eq_right_nonloop
          (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
          he hf hvef hxv hyv hxy
      · exact suppressPair_diestelDegree_eq_of_not_endpoint
          (G := G) (v := v) (x := x) (y := y) (a := a)
          (e := e) (f := f) he hf hvef hav hax hay

private def diestelDegreeTwoSet (G : MultiGraph V E) [Finite E] : Set V :=
  {v : V | v ∈ G.vertexSet ∧ G.diestelDegree v = 2}

private def diestelBranchVertexSetSelf (G : MultiGraph V E) [Finite E] : Set V :=
  {v : V | v ∈ G.vertexSet ∧ G.diestelDegree v = 3}

private lemma diestelBranchVertexSetSelf_subset_vertexSet
    (G : MultiGraph V E) [Finite E] :
    diestelBranchVertexSetSelf G ⊆ G.vertexSet := by
  intro v hv
  exact hv.1

private lemma suppressPair_branchVertexSetSelf_subset {G : MultiGraph V E}
    [Finite E] {v x y : V} {e f : E}
    (hvdeg : G.diestelDegree v = 2)
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    diestelBranchVertexSetSelf G ⊆
      diestelBranchVertexSetSelf (suppressPair G v x y e f) := by
  intro a ha
  have hav : a ≠ v := by
    intro hav
    have hdeg_a : G.diestelDegree a = 2 := by simpa [hav] using hvdeg
    have hdeg3 : G.diestelDegree a = 3 := ha.2
    omega
  have haH : a ∈ (suppressPair G v x y e f).vertexSet := by
    rw [suppressPair_vertexSet]
    exact ⟨ha.1, by simpa [Set.mem_singleton_iff] using hav⟩
  refine ⟨haH, ?_⟩
  rw [suppressPair_diestelDegree_eq_of_mem_vertexSet
    (G := G) (v := v) (x := x) (y := y) (a := a)
    (e := e) (f := f) hef he hf hvef hxv hyv haH]
  exact ha.2

private lemma suppressPair_branchVertexSetSelf_ncard_le {G : MultiGraph V E}
    [Finite V] [Finite E] {v x y : V} {e f : E}
    (hvdeg : G.diestelDegree v = 2)
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (diestelBranchVertexSetSelf G).ncard ≤
      (diestelBranchVertexSetSelf (suppressPair G v x y e f)).ncard :=
  Set.ncard_le_ncard
    (suppressPair_branchVertexSetSelf_subset
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      hvdeg hef he hf hvef hxv hyv)

private lemma suppressPair_degreeTwoSet_subset_diff {G : MultiGraph V E}
    [Finite E] {v x y : V} {e f : E}
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    diestelDegreeTwoSet (suppressPair G v x y e f) ⊆
      diestelDegreeTwoSet G \ {v} := by
  intro a ha
  have haH : a ∈ (suppressPair G v x y e f).vertexSet := ha.1
  rw [suppressPair_vertexSet] at haH
  refine ⟨⟨haH.1, ?_⟩, ?_⟩
  · rw [← suppressPair_diestelDegree_eq_of_mem_vertexSet
      (G := G) (v := v) (x := x) (y := y) (a := a)
      (e := e) (f := f) hef he hf hvef hxv hyv ha.1]
    exact ha.2
  · exact haH.2

private lemma suppressPair_degreeTwoSet_ncard_lt {G : MultiGraph V E}
    [Finite V] [Finite E] {v x y : V} {e f : E}
    (hvD : v ∈ diestelDegreeTwoSet G)
    (hef : e ≠ f) (he : G.IsLink e v x) (hf : G.IsLink f v y)
    (hvef : ∀ q : E, G.Incident v q → q = e ∨ q = f)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    (diestelDegreeTwoSet (suppressPair G v x y e f)).ncard <
      (diestelDegreeTwoSet G).ncard := by
  classical
  have hsubset :
      diestelDegreeTwoSet (suppressPair G v x y e f) ⊆
        diestelDegreeTwoSet G \ {v} :=
    suppressPair_degreeTwoSet_subset_diff
      (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
      hef he hf hvef hxv hyv
  have hle :
      (diestelDegreeTwoSet (suppressPair G v x y e f)).ncard ≤
        (diestelDegreeTwoSet G \ {v}).ncard :=
    Set.ncard_le_ncard hsubset
  have hdiff :
      (diestelDegreeTwoSet G \ {v}).ncard =
        (diestelDegreeTwoSet G).ncard - 1 := by
    rw [Set.ncard_diff (by
      intro z hz
      simpa [Set.mem_singleton_iff.mp hz] using hvD)]
    simp [hvD]
  have hpos : 0 < (diestelDegreeTwoSet G).ncard := by
    exact (Set.ncard_pos (s := diestelDegreeTwoSet G)).mpr ⟨v, hvD⟩
  omega

private noncomputable def deleteLoop_incidentEquiv {G : MultiGraph V E}
    {v a : V} {e : E}
    (hloop : G.IsLoopAt e v)
    (honly : ∀ g : E, G.Incident v g → g = e)
    (hav : a ≠ v) :
    {g : E // Incident (G.deleteVerts ({v} : Set V) : MultiGraph V E) a g} ≃
      {g : E // G.Incident a g} where
  toFun g :=
    ⟨g.1, ⟨(Graph.deleteVerts_le (G := G) (X := ({v} : Set V))).edgeSet_mono g.2.1,
      g.2.2.mono (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))⟩⟩
  invFun g := by
    rcases g with ⟨g, hg⟩
    let b : V := hg.2.other
    have hlink : G.IsLink g a b := hg.2.isLink_other
    have hbv : b ≠ v := by
      intro hbv
      have hgv : G.Incident v g :=
        ⟨hg.1, by simpa [hbv] using hlink.inc_right⟩
      have hge : g = e := honly g hgv
      subst g
      have hva : v = a := hloop.eq_of_inc hlink.inc_left
      exact hav hva.symm
    have hdel : (G.deleteVerts ({v} : Set V) : MultiGraph V E).Inc g a := by
      refine ⟨b, ?_⟩
      rw [Graph.deleteVerts_isLink]
      exact ⟨hlink, by simpa using hav, by simpa using hbv⟩
    exact ⟨g, ⟨hdel.edge_mem, hdel⟩⟩
  left_inv g := by
    ext
    rfl
  right_inv g := by
    ext
    rfl

private noncomputable def deleteLoop_loopEquiv {G : MultiGraph V E}
    {v a : V} {e : E}
    (hloop : G.IsLoopAt e v) (hav : a ≠ v) :
    {g : E // g ∈ loopSetAt (G.deleteVerts ({v} : Set V) : MultiGraph V E) a} ≃
      {g : E // g ∈ G.loopSetAt a} where
  toFun g :=
    ⟨g.1, ⟨(Graph.deleteVerts_le (G := G) (X := ({v} : Set V))).edgeSet_mono g.2.1,
      g.2.2.mono (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))⟩⟩
  invFun g := by
    rcases g with ⟨g, hg⟩
    have hdelLoop :
        (G.deleteVerts ({v} : Set V) : MultiGraph V E).IsLoopAt g a := by
      change (G.deleteVerts ({v} : Set V)).IsLink g a a
      rw [Graph.deleteVerts_isLink]
      exact ⟨hg.2, by simpa using hav, by simpa using hav⟩
    exact ⟨g, ⟨hdelLoop.edge_mem, hdelLoop⟩⟩
  left_inv g := by
    ext
    rfl
  right_inv g := by
    ext
    rfl

private lemma deleteLoop_diestelDegree_eq {G : MultiGraph V E}
    [Finite E] {v a : V} {e : E}
    (hloop : G.IsLoopAt e v)
    (honly : ∀ g : E, G.Incident v g → g = e)
    (hav : a ≠ v) :
    diestelDegree (G.deleteVerts ({v} : Set V) : MultiGraph V E) a =
      G.diestelDegree a := by
  change
    Nat.card {g : E // Incident (G.deleteVerts ({v} : Set V) : MultiGraph V E) a g} +
        Nat.card {g : E // g ∈
          loopSetAt (G.deleteVerts ({v} : Set V) : MultiGraph V E) a} =
      Nat.card {g : E // G.Incident a g} +
        Nat.card {g : E // g ∈ G.loopSetAt a}
  rw [Nat.card_congr (deleteLoop_incidentEquiv
      (G := G) (v := v) (a := a) (e := e) hloop honly hav),
    Nat.card_congr (deleteLoop_loopEquiv
      (G := G) (v := v) (a := a) (e := e) hloop hav)]

private lemma deleteLoop_branchVertexSetSelf_subset {G : MultiGraph V E}
    [Finite E] {v : V} {e : E}
    (hvdeg : G.diestelDegree v = 2)
    (hloop : G.IsLoopAt e v)
    (honly : ∀ g : E, G.Incident v g → g = e) :
    diestelBranchVertexSetSelf G ⊆
      diestelBranchVertexSetSelf (G.deleteVerts ({v} : Set V) : MultiGraph V E) := by
  intro a ha
  have hav : a ≠ v := by
    intro hav
    have hdeg_a : G.diestelDegree a = 2 := by simpa [hav] using hvdeg
    have hdeg3 : G.diestelDegree a = 3 := ha.2
    omega
  have haDel : a ∈ (G.deleteVerts ({v} : Set V)).vertexSet := by
    rw [Graph.vertexSet_deleteVerts]
    exact ⟨ha.1, by simpa [Set.mem_singleton_iff] using hav⟩
  refine ⟨haDel, ?_⟩
  rw [deleteLoop_diestelDegree_eq
    (G := G) (v := v) (a := a) (e := e) hloop honly hav]
  exact ha.2

private lemma deleteLoop_branchVertexSetSelf_ncard_le {G : MultiGraph V E}
    [Finite V] [Finite E] {v : V} {e : E}
    (hvdeg : G.diestelDegree v = 2)
    (hloop : G.IsLoopAt e v)
    (honly : ∀ g : E, G.Incident v g → g = e) :
    (diestelBranchVertexSetSelf G).ncard ≤
      (diestelBranchVertexSetSelf
        (G.deleteVerts ({v} : Set V) : MultiGraph V E)).ncard :=
  Set.ncard_le_ncard
    (deleteLoop_branchVertexSetSelf_subset
      (G := G) (v := v) (e := e) hvdeg hloop honly)

private lemma deleteLoop_degreeTwoSet_subset_diff {G : MultiGraph V E}
    [Finite E] {v : V} {e : E}
    (hloop : G.IsLoopAt e v)
    (honly : ∀ g : E, G.Incident v g → g = e) :
    diestelDegreeTwoSet (G.deleteVerts ({v} : Set V) : MultiGraph V E) ⊆
      diestelDegreeTwoSet G \ {v} := by
  intro a ha
  have haDel : a ∈ (G.deleteVerts ({v} : Set V)).vertexSet := ha.1
  rw [Graph.vertexSet_deleteVerts] at haDel
  have hav : a ≠ v := by
    intro hav
    exact haDel.2 (by simp [hav])
  refine ⟨⟨haDel.1, ?_⟩, ?_⟩
  · rw [← deleteLoop_diestelDegree_eq
      (G := G) (v := v) (a := a) (e := e) hloop honly hav]
    exact ha.2
  · exact haDel.2

private lemma deleteLoop_degreeTwoSet_ncard_lt {G : MultiGraph V E}
    [Finite V] [Finite E] {v : V} {e : E}
    (hvD : v ∈ diestelDegreeTwoSet G)
    (hloop : G.IsLoopAt e v)
    (honly : ∀ g : E, G.Incident v g → g = e) :
    (diestelDegreeTwoSet
        (G.deleteVerts ({v} : Set V) : MultiGraph V E)).ncard <
      (diestelDegreeTwoSet G).ncard := by
  classical
  have hsubset :
      diestelDegreeTwoSet (G.deleteVerts ({v} : Set V) : MultiGraph V E) ⊆
        diestelDegreeTwoSet G \ {v} :=
    deleteLoop_degreeTwoSet_subset_diff
      (G := G) (v := v) (e := e) hloop honly
  have hle :
      (diestelDegreeTwoSet
          (G.deleteVerts ({v} : Set V) : MultiGraph V E)).ncard ≤
        (diestelDegreeTwoSet G \ {v}).ncard :=
    Set.ncard_le_ncard hsubset
  have hdiff :
      (diestelDegreeTwoSet G \ {v}).ncard =
        (diestelDegreeTwoSet G).ncard - 1 := by
    rw [Set.ncard_diff (by
      intro z hz
      simpa [Set.mem_singleton_iff.mp hz] using hvD)]
    simp [hvD]
  have hpos : 0 < (diestelDegreeTwoSet G).ncard := by
    exact (Set.ncard_pos (s := diestelDegreeTwoSet G)).mpr ⟨v, hvD⟩
  omega

private def HasSelfDiestelSuppressedCubicKernel
    (G : MultiGraph V E) [Finite V] [Finite E] : Prop :=
  ∃ V' : Type u, ∃ E' : Type v,
    ∃ hfinV' : Finite V', ∃ hfinE' : Finite E',
    ∃ H : MultiGraph V' E',
      @IsDiestelCubic V' E' H hfinE' ∧
        (diestelBranchVertexSetSelf G).ncard ≤ H.vertexSet.ncard ∧
          DiestelCyclePackingTransfer H G

private lemma hasSelfDiestelSuppressedCubicKernel_of_degreeTwoSet_eq_empty
    {G : MultiGraph V E} [Finite V] [Finite E]
    (hle3 : ∀ a : V, a ∈ G.vertexSet → G.diestelDegree a ≤ 3)
    (hge2 : ∀ a : V, a ∈ G.vertexSet → 2 ≤ G.diestelDegree a)
    (hD₂ : diestelDegreeTwoSet G = ∅) :
    HasSelfDiestelSuppressedCubicKernel G := by
  refine ⟨V, E, inferInstance, inferInstance, G, ?_, ?_, ?_⟩
  · intro a ha
    have hle : G.diestelDegree a ≤ 3 := hle3 a ha
    have hge : 2 ≤ G.diestelDegree a := hge2 a ha
    have hne : G.diestelDegree a ≠ 2 := by
      intro hdeg
      have haD : a ∈ diestelDegreeTwoSet G := ⟨ha, hdeg⟩
      rw [hD₂] at haD
      simp at haD
    omega
  · exact Set.ncard_le_ncard (diestelBranchVertexSetSelf_subset_vertexSet G)
  · intro k hpack
    exact hpack

private theorem hasSelfDiestelSuppressedCubicKernel_of_degree_bounds :
    ∀ {V : Type u} {E : Type v} (G : MultiGraph V E) [Finite V] [Finite E],
      (∀ a : V, a ∈ G.vertexSet → G.diestelDegree a ≤ 3) →
      (∀ a : V, a ∈ G.vertexSet → 2 ≤ G.diestelDegree a) →
      HasSelfDiestelSuppressedCubicKernel G := by
  intro V E G hfinV hfinE
  let n := (diestelDegreeTwoSet G).ncard
  suffices
      ∀ {V : Type u} {E : Type v} (G : MultiGraph V E) [Finite V] [Finite E],
        (diestelDegreeTwoSet G).ncard = n →
        (∀ a : V, a ∈ G.vertexSet → G.diestelDegree a ≤ 3) →
        (∀ a : V, a ∈ G.vertexSet → 2 ≤ G.diestelDegree a) →
        HasSelfDiestelSuppressedCubicKernel G by
    intro hle3 hge2
    exact this G rfl hle3 hge2
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V E G hfinV hfinE hn hle3 hge2
      by_cases hD₂ : diestelDegreeTwoSet G = ∅
      · exact hasSelfDiestelSuppressedCubicKernel_of_degreeTwoSet_eq_empty
          (G := G) hle3 hge2 hD₂
      · have hDnonempty : (diestelDegreeTwoSet G).Nonempty := by
          rwa [Set.nonempty_iff_ne_empty]
        rcases hDnonempty with ⟨v, hvD⟩
        have hvdeg : G.diestelDegree v = 2 := hvD.2
        rcases diestelDegree_eq_two_cases (G := G) hvdeg with hloopCase | hlinkCase
        · rcases hloopCase with ⟨e, hloop, honly⟩
          let Gdel : MultiGraph V E := G.deleteVerts ({v} : Set V)
          have hmeasure :
              (diestelDegreeTwoSet Gdel).ncard < n := by
            rw [← hn]
            exact deleteLoop_degreeTwoSet_ncard_lt
              (G := G) (v := v) (e := e) hvD hloop honly
          have hle3del :
              ∀ a : V, a ∈ Gdel.vertexSet → Gdel.diestelDegree a ≤ 3 := by
            intro a ha
            have ha' := ha
            change a ∈ (G.deleteVerts ({v} : Set V)).vertexSet at ha'
            rw [Graph.vertexSet_deleteVerts] at ha'
            have hav : a ≠ v := by
              intro hav
              exact ha'.2 (by simp [hav])
            rw [deleteLoop_diestelDegree_eq
              (G := G) (v := v) (a := a) (e := e) hloop honly hav]
            exact hle3 a ha'.1
          have hge2del :
              ∀ a : V, a ∈ Gdel.vertexSet → 2 ≤ Gdel.diestelDegree a := by
            intro a ha
            have ha' := ha
            change a ∈ (G.deleteVerts ({v} : Set V)).vertexSet at ha'
            rw [Graph.vertexSet_deleteVerts] at ha'
            have hav : a ≠ v := by
              intro hav
              exact ha'.2 (by simp [hav])
            rw [deleteLoop_diestelDegree_eq
              (G := G) (v := v) (a := a) (e := e) hloop honly hav]
            exact hge2 a ha'.1
          obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranch, htransfer⟩ :=
            ih (diestelDegreeTwoSet Gdel).ncard hmeasure Gdel rfl hle3del hge2del
          refine ⟨V', E', hfinV', hfinE', H, hHCubic, ?_, ?_⟩
          · exact (deleteLoop_branchVertexSetSelf_ncard_le
              (G := G) (v := v) (e := e) hvdeg hloop honly).trans hbranch
          · intro k hpack
            exact hasKDisjointDiestelCycles_of_subgraph
              (Graph.deleteVerts_le (G := G) (X := ({v} : Set V)))
              (htransfer k hpack)
        · rcases hlinkCase with ⟨e, f, x, y, hef, hxv, hyv, he, hf, hvef⟩
          let H₀ : MultiGraph V (StepEdge E) := suppressPair G v x y e f
          haveI : Finite (StepEdge E) := inferInstance
          have hmeasure :
              (diestelDegreeTwoSet H₀).ncard < n := by
            rw [← hn]
            exact suppressPair_degreeTwoSet_ncard_lt
              (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
              hvD hef he hf hvef hxv hyv
          have hle3H₀ :
              ∀ a : V, a ∈ H₀.vertexSet → H₀.diestelDegree a ≤ 3 := by
            intro a ha
            rw [suppressPair_diestelDegree_eq_of_mem_vertexSet
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) hef he hf hvef hxv hyv ha]
            exact hle3 a (suppressPair_vertexSet_subset (G := G)
              (v := v) (x := x) (y := y) (e := e) (f := f) ha)
          have hge2H₀ :
              ∀ a : V, a ∈ H₀.vertexSet → 2 ≤ H₀.diestelDegree a := by
            intro a ha
            rw [suppressPair_diestelDegree_eq_of_mem_vertexSet
              (G := G) (v := v) (x := x) (y := y) (a := a)
              (e := e) (f := f) hef he hf hvef hxv hyv ha]
            exact hge2 a (suppressPair_vertexSet_subset (G := G)
              (v := v) (x := x) (y := y) (e := e) (f := f) ha)
          obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranch, htransfer⟩ :=
            ih (diestelDegreeTwoSet H₀).ncard hmeasure H₀ rfl hle3H₀ hge2H₀
          refine ⟨V', E', hfinV', hfinE', H, hHCubic, ?_, ?_⟩
          · exact (suppressPair_branchVertexSetSelf_ncard_le
              (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
              hvdeg hef he hf hvef hxv hyv).trans hbranch
          · intro k hpack
            rcases htransfer k hpack with ⟨C, hdisj⟩
            exact hasKDisjointDiestelCycles_of_suppressPair
              (G := G) (v := v) (x := x) (y := y) (e := e) (f := f)
              C hdisj hef he hf hvef hxv hyv

theorem exists_diestelSuppressedCubicKernel_of_degree_bounds
    {V : Type u} {E : Type v} (G : MultiGraph V E) [Finite V] [Finite E]
    (hle3 : ∀ a : V, a ∈ G.vertexSet → G.diestelDegree a ≤ 3)
    (hge2 : ∀ a : V, a ∈ G.vertexSet → 2 ≤ G.diestelDegree a) :
    ∃ V' : Type u, ∃ E' : Type v,
      ∃ hfinV' : Finite V', ∃ hfinE' : Finite E',
      ∃ H : MultiGraph V' E',
        @IsDiestelCubic V' E' H hfinE' ∧
          ({v : V | v ∈ G.vertexSet ∧ G.diestelDegree v = 3}).ncard ≤
            H.vertexSet.ncard ∧
            DiestelCyclePackingTransfer H G := by
  classical
  obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranch, htransfer⟩ :=
    hasSelfDiestelSuppressedCubicKernel_of_degree_bounds G hle3 hge2
  refine ⟨V', E', hfinV', hfinE', H, hHCubic, ?_, htransfer⟩
  exact hbranch

private lemma diestelBranchVertexSet_ncard_le_self_delete
    {G : MultiGraph V E} [Finite V] [Finite E] (U : Set V) :
    (diestelBranchVertexSet G U).ncard ≤
      (diestelBranchVertexSetSelf
        (G.deleteVerts U : MultiGraph V E)).ncard := by
  refine Set.ncard_le_ncard ?_
  intro a ha
  change a ∈ G.vertexSet ∧ a ∉ U ∧
    diestelDegree (G.deleteVerts U : MultiGraph V E) a = 3 at ha
  change a ∈ (G.deleteVerts U : MultiGraph V E).vertexSet ∧
    diestelDegree (G.deleteVerts U : MultiGraph V E) a = 3
  rw [Graph.vertexSet_deleteVerts]
  exact ⟨⟨ha.1, ha.2.1⟩, ha.2.2⟩

theorem hasDiestelSuppressedCubicKernel_of_terminal {G : MultiGraph V E}
    [Finite V] [Finite E] (hCubic : G.IsDiestelCubic) {U : Set V}
    (hterminal : ∀ v : V, v ∈ G.vertexSet → v ∉ U →
      2 ≤ diestelDegree (G.deleteVerts U : MultiGraph V E) v) :
    HasDiestelSuppressedCubicKernel G U := by
  let Gdel : MultiGraph V E := G.deleteVerts U
  have hle3 :
      ∀ a : V, a ∈ Gdel.vertexSet → Gdel.diestelDegree a ≤ 3 := by
    intro a ha
    change a ∈ (G.deleteVerts U).vertexSet at ha
    rw [Graph.vertexSet_deleteVerts] at ha
    exact deleteVerts_diestelDegree_le_three_of_cubic
      (G := G) hCubic ha.1
  have hge2 :
      ∀ a : V, a ∈ Gdel.vertexSet → 2 ≤ Gdel.diestelDegree a := by
    intro a ha
    change a ∈ (G.deleteVerts U).vertexSet at ha
    rw [Graph.vertexSet_deleteVerts] at ha
    exact hterminal a ha.1 ha.2
  obtain ⟨V', E', hfinV', hfinE', H, hHCubic, hbranch, htransfer⟩ :=
    hasSelfDiestelSuppressedCubicKernel_of_degree_bounds Gdel hle3 hge2
  refine ⟨V', E', hfinV', hfinE', H, hHCubic, ?_, htransfer⟩
  exact (diestelBranchVertexSet_ncard_le_self_delete (G := G) U).trans hbranch

theorem lemma_2_3_1_diestel {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ) :
    G.IsDiestelCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointDiestelCycles k := by
  exact lemma_2_3_1_diestel_from_reductions
    (fun G _hfinV _hfinE k hk hCubic hLarge =>
      hasDiestelCyclePackingReduction_of_suppressed_kernel'
        (G := G) (k := k) hk
        (fun _C _U _hCU _hUV _hscore hterminal =>
          hasDiestelSuppressedCubicKernel_of_terminal
            (G := G) hCubic hterminal)
        hCubic hLarge)
    G k

theorem lemma_2_3_1_diestel_ge {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ) :
    G.IsDiestelCubic →
      erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointDiestelCycles k := by
  exact lemma_2_3_1_diestel_from_reductions_ge
    (fun G _hfinV _hfinE k hk hCubic hLarge =>
      hasDiestelCyclePackingReduction_of_suppressed_kernel_ge'
        (G := G) (k := k) hk
        (fun _C _U _hCU _hUV _hscore hterminal =>
          hasDiestelSuppressedCubicKernel_of_terminal
            (G := G) hCubic hterminal)
        hCubic hLarge)
    G k

theorem lemma_2_3_1_loopless {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ) :
    G.IsCubic →
      erdosPosaS k < (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointCycles k := by
  intro hCubic hLarge
  have hDpack : G.HasKDisjointDiestelCycles k :=
    lemma_2_3_1_diestel G k
      (isDiestelCubic_of_isCubic (G := G) hCubic) hLarge
  exact hasKDisjointCycles_of_hasKDisjointDiestelCycles_of_loopless
    (G := G) hCubic.1 hDpack

theorem lemma_2_3_1_loopless_ge {V : Type u} {E : Type v}
    (G : MultiGraph V E) [Finite V] [Finite E] (k : ℕ) :
    G.IsCubic →
      erdosPosaS k ≤ (G.vertexSet.ncard : ℝ) →
        G.HasKDisjointCycles k := by
  intro hCubic hLarge
  have hDpack : G.HasKDisjointDiestelCycles k :=
    lemma_2_3_1_diestel_ge G k
      (isDiestelCubic_of_isCubic (G := G) hCubic) hLarge
  exact hasKDisjointCycles_of_hasKDisjointDiestelCycles_of_loopless
    (G := G) hCubic.1 hDpack

lemma suppressPair_new_edge_mem_unique_in_disjoint_cycles {G : MultiGraph V E}
    {v x y : V} {e f : E} {k : ℕ}
    {C : Fin k → (suppressPair G v x y e f).DiestelCycleIn}
    (hdisj : Pairwise fun i j => Disjoint (C i).support (C j).support)
    {i j : Fin k} (hij : i ≠ j)
    (hi : Sum.inr () ∈ (C i).edgeSupport)
    (hj : Sum.inr () ∈ (C j).edgeSupport) :
    False := by
  have hxi : x ∈ (C i).support :=
    (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
      (x := x) (y := y) (e := e) (f := f) (C i) hi).1
  have hxj : x ∈ (C j).support :=
    (suppressPair_new_edge_endpoint_mem_support (G := G) (v := v)
      (x := x) (y := y) (e := e) (f := f) (C j) hj).1
  exact (Set.disjoint_left.mp (hdisj hij)) hxi hxj

end Suppression

end MultiGraph

end Chapter02
end Diestel
