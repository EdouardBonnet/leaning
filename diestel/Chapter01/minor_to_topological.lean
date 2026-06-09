import Chapter01.three_fan

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

private theorem source_edge_adj {W : Type u} {X : SimpleGraph W} (e : X.edgeSet) :
    X.Adj (e : Sym2 W).out.1 (e : Sym2 W).out.2 := by
  have he : (e : Sym2 W) ∈ X.edgeSet := e.2
  rw [← (e : Sym2 W).out_eq] at he
  exact (SimpleGraph.mem_edgeSet X).mp he

private noncomputable def modelEdgeLeft {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) : V :=
  Classical.choose (M.adjacent (source_edge_adj e))

private theorem modelEdgeLeft_mem {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) :
    modelEdgeLeft M e ∈ M.branchSet (e : Sym2 W).out.1 :=
  (Classical.choose_spec (M.adjacent (source_edge_adj e))).1

private noncomputable def modelEdgeRight {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) : V :=
  Classical.choose (Classical.choose_spec (M.adjacent (source_edge_adj e))).2

private theorem modelEdgeRight_mem {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) :
    modelEdgeRight M e ∈ M.branchSet (e : Sym2 W).out.2 :=
  (Classical.choose_spec
    (Classical.choose_spec (M.adjacent (source_edge_adj e))).2).1

private theorem modelEdge_adj {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) :
    G.Adj (modelEdgeLeft M e) (modelEdgeRight M e) :=
  (Classical.choose_spec
    (Classical.choose_spec (M.adjacent (source_edge_adj e))).2).2

private noncomputable def incidentEdgeFinset {W : Type u} (X : SimpleGraph W) [Fintype W]
    [DecidableRel X.Adj] (x : W) : Finset X.edgeSet := by
  classical
  exact Finset.univ.filter fun e : X.edgeSet => x ∈ (e : Sym2 W)

private theorem mem_incidentEdgeFinset {W : Type u} (X : SimpleGraph W) [Fintype W]
    [DecidableRel X.Adj] (x : W) (e : X.edgeSet) :
    e ∈ incidentEdgeFinset X x ↔ x ∈ (e : Sym2 W) := by
  classical
  simp [incidentEdgeFinset]

private noncomputable def edgePort {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (x : W) (e : X.edgeSet) : V :=
  by
    classical
    exact if (e : Sym2 W).out.1 = x then modelEdgeLeft M e else modelEdgeRight M e

private theorem edgePort_mem {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    {x : W} {e : X.edgeSet} (he : x ∈ (e : Sym2 W)) :
    edgePort M x e ∈ M.branchSet x := by
  classical
  unfold edgePort
  by_cases hleft : (e : Sym2 W).out.1 = x
  · simpa [hleft] using modelEdgeLeft_mem M e
  · have hxright : (e : Sym2 W).out.2 = x := by
      have hx : x = (e : Sym2 W).out.1 ∨ x = (e : Sym2 W).out.2 := by
        have he' : x ∈ s((e : Sym2 W).out.1, (e : Sym2 W).out.2) := by
          simpa [Sym2.mk, (e : Sym2 W).out_eq] using he
        simpa [Sym2.mem_iff] using he'
      exact (hx.resolve_left (fun hx => hleft hx.symm)).symm
    simpa [hleft, hxright] using modelEdgeRight_mem M e

private noncomputable def branchPorts {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (x : W) : Finset V := by
  classical
  exact (incidentEdgeFinset X x).image (fun e => edgePort M x e)

private theorem mem_branchPorts {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (x : W) {p : V} :
    p ∈ branchPorts M x →
      p ∈ M.branchSet x := by
  classical
  intro hp
  rw [branchPorts, Finset.mem_image] at hp
  rcases hp with ⟨e, he, rfl⟩
  exact edgePort_mem M ((mem_incidentEdgeFinset X x e).mp he)

private theorem incidentEdgeFinset_card_le_degree {W : Type u}
    (X : SimpleGraph W) [Fintype W] [DecidableRel X.Adj] (x : W) :
    (incidentEdgeFinset X x).card ≤ X.degree x := by
  classical
  let f : X.edgeSet → Sym2 W := fun e => (e : Sym2 W)
  have hinj : Function.Injective f := by
    intro e e' h
    exact Subtype.ext h
  have hcard_image :
      ((incidentEdgeFinset X x).image f).card = (incidentEdgeFinset X x).card := by
    exact Finset.card_image_of_injective _ hinj
  have hsub : (incidentEdgeFinset X x).image f ⊆ X.incidenceFinset x := by
    intro e he
    rw [Finset.mem_image] at he
    rcases he with ⟨e', he', rfl⟩
    rw [X.mem_incidenceFinset]
    rw [X.edge_mem_incidenceSet_iff]
    exact (mem_incidentEdgeFinset X x e').mp he'
  calc
    (incidentEdgeFinset X x).card = ((incidentEdgeFinset X x).image f).card := hcard_image.symm
    _ ≤ (X.incidenceFinset x).card := Finset.card_le_card hsub
    _ = X.degree x := X.card_incidenceFinset_eq_degree x

private theorem branchPorts_card_le_three {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3) (x : W) :
    (branchPorts M x).card ≤ 3 := by
  classical
  calc
    (branchPorts M x).card ≤ (incidentEdgeFinset X x).card := by
      unfold branchPorts
      exact Finset.card_image_le
    _ ≤ X.degree x := incidentEdgeFinset_card_le_degree X x
    _ ≤ X.maxDegree := X.degree_le_maxDegree x
    _ ≤ 3 := hmax

private theorem edgePort_mem_branchPorts {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (x : W) (e : X.edgeSet) (he : x ∈ (e : Sym2 W)) :
    edgePort M x e ∈ branchPorts M x := by
  classical
  unfold branchPorts
  rw [Finset.mem_image]
  exact ⟨e, (mem_incidentEdgeFinset X x e).mpr he, rfl⟩

private theorem edgePort_left {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) :
    edgePort M (e : Sym2 W).out.1 e = modelEdgeLeft M e := by
  classical
  simp [edgePort]

private theorem edgePort_right {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} (M : Model X G)
    (e : X.edgeSet) :
    edgePort M (e : Sym2 W).out.2 e = modelEdgeRight M e := by
  classical
  have hne : (e : Sym2 W).out.1 ≠ (e : Sym2 W).out.2 :=
    (source_edge_adj e).ne
  simp [edgePort, hne]

private theorem source_edge_fst_incident {W : Type u}
    {X : SimpleGraph W} [Fintype W] [DecidableRel X.Adj] (e : X.edgeSet) :
    e ∈ incidentEdgeFinset X (e : Sym2 W).out.1 :=
  (mem_incidentEdgeFinset X (e : Sym2 W).out.1 e).mpr (Sym2.out_fst_mem _)

private theorem source_edge_snd_incident {W : Type u}
    {X : SimpleGraph W} [Fintype W] [DecidableRel X.Adj] (e : X.edgeSet) :
    e ∈ incidentEdgeFinset X (e : Sym2 W).out.2 :=
  (mem_incidentEdgeFinset X (e : Sym2 W).out.2 e).mpr (Sym2.out_snd_mem _)

private theorem incidentEdgeFinset_card_le_three {W : Type u}
    {X : SimpleGraph W} [Fintype W] [DecidableRel X.Adj]
    (hmax : X.maxDegree ≤ 3) (x : W) :
    (incidentEdgeFinset X x).card ≤ 3 := by
  calc
    (incidentEdgeFinset X x).card ≤ X.degree x := incidentEdgeFinset_card_le_degree X x
    _ ≤ X.maxDegree := X.degree_le_maxDegree x
    _ ≤ 3 := hmax

private noncomputable def branchIndexedFan {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3) (x : W) :
    IndexedFan G (M.branchSet x) (incidentEdgeFinset X x) (edgePort M x) :=
  by
    classical
    exact Classical.choose
      (exists_indexedFan_of_card_le_three (incidentEdgeFinset X x) (edgePort M x)
        (M.connected x)
        (fun e he => edgePort_mem M ((mem_incidentEdgeFinset X x e).mp he))
        (incidentEdgeFinset_card_le_three hmax x))

private theorem branchIndexedFan_center_mem {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3) (x : W) :
    (branchIndexedFan M hmax x).center ∈ M.branchSet x :=
  (branchIndexedFan M hmax x).center_mem

private theorem branchIndexedFan_center_injective {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3) :
    Function.Injective fun x : W => (branchIndexedFan M hmax x).center := by
  intro x y hxy
  by_contra hne
  have hdisj := M.pairwise_disjoint hne
  change Disjoint (M.branchSet x) (M.branchSet y) at hdisj
  rw [Set.disjoint_left] at hdisj
  exact hdisj (branchIndexedFan_center_mem M hmax x) (by
    simpa [hxy] using branchIndexedFan_center_mem M hmax y)

private noncomputable def canonicalEdgeWalk {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3) (e : X.edgeSet) :
    G.Walk (branchIndexedFan M hmax (e : Sym2 W).out.1).center
      (branchIndexedFan M hmax (e : Sym2 W).out.2).center := by
  classical
  let F₁ := branchIndexedFan M hmax (e : Sym2 W).out.1
  let F₂ := branchIndexedFan M hmax (e : Sym2 W).out.2
  let p₁raw := F₁.arm e (source_edge_fst_incident e)
  let p₂raw := F₂.arm e (source_edge_snd_incident e)
  let p₁ : G.Walk F₁.center (modelEdgeLeft M e) :=
    p₁raw.copy rfl (edgePort_left M e)
  let p₂ : G.Walk F₂.center (modelEdgeRight M e) :=
    p₂raw.copy rfl (edgePort_right M e)
  exact p₁.append (SimpleGraph.Walk.cons (modelEdge_adj M e) p₂.reverse)

private theorem source_edge_eq_of_out_mk {W : Type u} {X : SimpleGraph W}
    {x y : W} (e : X.edgeSet) (he : (e : Sym2 W) = s(x, y)) :
    (e : Sym2 W).out.1 = x ∧ (e : Sym2 W).out.2 = y ∨
      (e : Sym2 W).out.1 = y ∧ (e : Sym2 W).out.2 = x := by
  have hout : s((e : Sym2 W).out.1, (e : Sym2 W).out.2) = s(x, y) := by
    rw [Sym2.mk, (e : Sym2 W).out_eq, he]
  simpa using Sym2.eq_iff.mp hout

private noncomputable def sourceEdgeOfAdj {W : Type u} {X : SimpleGraph W}
    {x y : W} (hxy : X.Adj x y) : X.edgeSet :=
  ⟨s(x, y), (SimpleGraph.mem_edgeSet X).mpr hxy⟩

private theorem sourceEdgeOfAdj_left_incident {W : Type u}
    {X : SimpleGraph W} [Fintype W] [DecidableRel X.Adj]
    {x y : W} (hxy : X.Adj x y) :
    sourceEdgeOfAdj hxy ∈ incidentEdgeFinset X x := by
  rw [mem_incidentEdgeFinset]
  change x ∈ s(x, y)
  simp [Sym2.mem_iff]

private theorem sourceEdgeOfAdj_right_incident {W : Type u}
    {X : SimpleGraph W} [Fintype W] [DecidableRel X.Adj]
    {x y : W} (hxy : X.Adj x y) :
    sourceEdgeOfAdj hxy ∈ incidentEdgeFinset X y := by
  rw [mem_incidentEdgeFinset]
  change y ∈ s(x, y)
  simp [Sym2.mem_iff]

private theorem sourceEdgeOfAdj_ne_of_sym2_ne {W : Type u}
    {X : SimpleGraph W} {x y z w : W}
    (hxy : X.Adj x y) (hzw : X.Adj z w)
    (hne : s(x, y) ≠ s(z, w)) :
    sourceEdgeOfAdj hxy ≠ sourceEdgeOfAdj hzw := by
  intro hef
  exact hne (by
    simpa [sourceEdgeOfAdj] using congrArg (fun e : X.edgeSet => (e : Sym2 W)) hef)

private noncomputable def modelEdgePath {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3)
    {x y : W} (hxy : X.Adj x y) :
    G.Walk (branchIndexedFan M hmax x).center (branchIndexedFan M hmax y).center := by
  classical
  let e : X.edgeSet := sourceEdgeOfAdj hxy
  have he : (e : Sym2 W) = s(x, y) := rfl
  have hcases := source_edge_eq_of_out_mk e he
  if hor : (e : Sym2 W).out.1 = x ∧ (e : Sym2 W).out.2 = y then
    exact (canonicalEdgeWalk M hmax e).copy (by rw [hor.1]) (by rw [hor.2])
  else
    have hor' : (e : Sym2 W).out.1 = y ∧ (e : Sym2 W).out.2 = x :=
      hcases.resolve_left hor
    exact (canonicalEdgeWalk M hmax e).reverse.copy (by rw [hor'.2]) (by rw [hor'.1])

private noncomputable def modelEdgePathBypass {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    [DecidableEq V]
    (M : Model X G) (hmax : X.maxDegree ≤ 3)
    {x y : W} (hxy : X.Adj x y) :
    G.Walk (branchIndexedFan M hmax x).center (branchIndexedFan M hmax y).center :=
  (modelEdgePath M hmax hxy).bypass

private theorem modelEdgePathBypass_isPath {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    [DecidableEq V]
    (M : Model X G) (hmax : X.maxDegree ≤ 3)
    {x y : W} (hxy : X.Adj x y) :
    (modelEdgePathBypass M hmax hxy).IsPath :=
  SimpleGraph.Walk.bypass_isPath _

private theorem canonicalEdgeWalk_support_cases {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
      (M : Model X G) (hmax : X.maxDegree ≤ 3) (e : X.edgeSet) {z : V}
      (hz : z ∈ (canonicalEdgeWalk M hmax e).support) :
      z ∈ ((branchIndexedFan M hmax (e : Sym2 W).out.1).arm e
          (source_edge_fst_incident e)).support ∨
        z ∈ ((branchIndexedFan M hmax (e : Sym2 W).out.2).arm e
          (source_edge_snd_incident e)).support := by
    classical
    unfold canonicalEdgeWalk at hz
    dsimp at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · left
      simpa [edgePort_left] using hz
    · rw [SimpleGraph.Walk.support_cons] at hz
      simp only [List.mem_cons] at hz
      rcases hz with hhead | htail
      · left
        simpa [edgePort_left, hhead] using
          (((branchIndexedFan M hmax (e : Sym2 W).out.1).arm e
            (source_edge_fst_incident e)).end_mem_support)
      · right
        rw [SimpleGraph.Walk.support_reverse] at htail
        simpa [SimpleGraph.Walk.support_copy, edgePort_right] using htail

  private theorem canonicalEdgeWalk_support_branchSet {V : Type u} {W : Type v}
      {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
      (M : Model X G) (hmax : X.maxDegree ≤ 3) (e : X.edgeSet) {z : V}
      (hz : z ∈ (canonicalEdgeWalk M hmax e).support) :
      z ∈ M.branchSet (e : Sym2 W).out.1 ∨
        z ∈ M.branchSet (e : Sym2 W).out.2 := by
    classical
    rcases canonicalEdgeWalk_support_cases M hmax e hz with hz | hz
    · left
      exact (branchIndexedFan M hmax (e : Sym2 W).out.1).arm_support_subset _ _ z hz
    · right
      exact (branchIndexedFan M hmax (e : Sym2 W).out.2).arm_support_subset _ _ z hz

private theorem modelEdgePathBypass_support_branchSet {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    [DecidableEq V]
    (M : Model X G) (hmax : X.maxDegree ≤ 3)
    {x y : W} (hxy : X.Adj x y) {z : V}
      (hz : z ∈ (modelEdgePathBypass M hmax hxy).support) :
      z ∈ M.branchSet x ∨ z ∈ M.branchSet y := by
    classical
    have hzraw : z ∈ (modelEdgePath M hmax hxy).support :=
      SimpleGraph.Walk.support_bypass_subset _ hz
    let e : X.edgeSet := sourceEdgeOfAdj hxy
    have he : (e : Sym2 W) = s(x, y) := rfl
    unfold modelEdgePath at hzraw
    dsimp at hzraw
    split_ifs at hzraw with hor
    · have hzcanon : z ∈ (canonicalEdgeWalk M hmax e).support := by
        simpa [e] using hzraw
      rcases canonicalEdgeWalk_support_branchSet M hmax e hzcanon with hz1 | hz2
      · left
        simpa [e, hor.1] using hz1
      · right
        simpa [e, hor.2] using hz2
    · have hor' : (e : Sym2 W).out.1 = y ∧ (e : Sym2 W).out.2 = x :=
        (source_edge_eq_of_out_mk e he).resolve_left hor
      have hzcanon : z ∈ (canonicalEdgeWalk M hmax e).support := by
        have hzrev : z ∈ (canonicalEdgeWalk M hmax e).reverse.support := by
          simpa [e] using hzraw
        rw [SimpleGraph.Walk.support_reverse] at hzrev
        simpa using hzrev
      rcases canonicalEdgeWalk_support_branchSet M hmax e hzcanon with hz1 | hz2
      · right
        simpa [e, hor'.1] using hz1
      · left
        simpa [e, hor'.2] using hz2

private theorem modelEdgePathBypass_support_cases {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    [DecidableEq V]
      (M : Model X G) (hmax : X.maxDegree ≤ 3)
      {x y : W} (hxy : X.Adj x y) {z : V}
      (hz : z ∈ (modelEdgePathBypass M hmax hxy).support) :
      ∃ a : W, (a = x ∨ a = y) ∧
        ∃ he : sourceEdgeOfAdj hxy ∈ incidentEdgeFinset X a,
          z ∈ ((branchIndexedFan M hmax a).arm (sourceEdgeOfAdj hxy) he).support := by
    classical
    have hzraw : z ∈ (modelEdgePath M hmax hxy).support :=
      SimpleGraph.Walk.support_bypass_subset _ hz
    let e : X.edgeSet := sourceEdgeOfAdj hxy
    have he : (e : Sym2 W) = s(x, y) := rfl
    unfold modelEdgePath at hzraw
    dsimp at hzraw
    split_ifs at hzraw with hor
    · have hzcanon : z ∈ (canonicalEdgeWalk M hmax e).support := by
        simpa [e] using hzraw
      rcases canonicalEdgeWalk_support_cases M hmax e hzcanon with hz1 | hz2
      · refine ⟨(e : Sym2 W).out.1, Or.inl (by simpa [e] using hor.1), ?_⟩
        refine ⟨by simpa [e] using source_edge_fst_incident e, ?_⟩
        simpa [e] using hz1
      · refine ⟨(e : Sym2 W).out.2, Or.inr (by simpa [e] using hor.2), ?_⟩
        refine ⟨by simpa [e] using source_edge_snd_incident e, ?_⟩
        simpa [e] using hz2
    · have hor' : (e : Sym2 W).out.1 = y ∧ (e : Sym2 W).out.2 = x :=
        (source_edge_eq_of_out_mk e he).resolve_left hor
      have hzcanon : z ∈ (canonicalEdgeWalk M hmax e).support := by
        have hzrev : z ∈ (canonicalEdgeWalk M hmax e).reverse.support := by
          simpa [e] using hzraw
        rw [SimpleGraph.Walk.support_reverse] at hzrev
        simpa using hzrev
      rcases canonicalEdgeWalk_support_cases M hmax e hzcanon with hz1 | hz2
      · refine ⟨(e : Sym2 W).out.1, Or.inr (by simpa [e] using hor'.1), ?_⟩
        refine ⟨by simpa [e] using source_edge_fst_incident e, ?_⟩
        simpa [e] using hz1
      · refine ⟨(e : Sym2 W).out.2, Or.inl (by simpa [e] using hor'.2), ?_⟩
        refine ⟨by simpa [e] using source_edge_snd_incident e, ?_⟩
        simpa [e] using hz2

private theorem modelEdgePathBypass_branch_not_inner {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    [DecidableEq V]
    (M : Model X G) (hmax : X.maxDegree ≤ 3)
    {x y z : W} (hxy : X.Adj x y) :
      (branchIndexedFan M hmax z).center ∈
          walk_inner_vertices (modelEdgePathBypass M hmax hxy) →
      False := by
    intro hinner
    have hsupport := modelEdgePathBypass_support_branchSet M hmax hxy hinner.1
    rcases hsupport with hxmem | hymem
    · by_cases hzx : z = x
      · subst z
        exact hinner.2.1 rfl
      · have hdisj := M.pairwise_disjoint hzx
        change Disjoint (M.branchSet z) (M.branchSet x) at hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj (branchIndexedFan_center_mem M hmax z) hxmem
    · by_cases hzy : z = y
      · subst z
        exact hinner.2.2 rfl
      · have hdisj := M.pairwise_disjoint hzy
        change Disjoint (M.branchSet z) (M.branchSet y) at hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj (branchIndexedFan_center_mem M hmax z) hymem

private theorem modelEdgePathBypass_inner_disjoint {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    [DecidableEq V]
    (M : Model X G) (hmax : X.maxDegree ≤ 3)
    {x y z w : W} (hxy : X.Adj x y) (hzw : X.Adj z w)
    (hne : s(x, y) ≠ s(z, w)) :
    Disjoint (walk_inner_vertices (modelEdgePathBypass M hmax hxy))
      (walk_inner_vertices (modelEdgePathBypass M hmax hzw)) := by
    rw [Set.disjoint_left]
    intro r hrP hrQ
    rcases modelEdgePathBypass_support_cases M hmax hxy hrP.1 with ⟨a, ha_endpoint, hea, hra⟩
    rcases modelEdgePathBypass_support_cases M hmax hzw hrQ.1 with ⟨b, _hb_endpoint, heb, hrb⟩
    by_cases hab : a = b
    · subst b
      have he_ne : sourceEdgeOfAdj hxy ≠ sourceEdgeOfAdj hzw :=
        sourceEdgeOfAdj_ne_of_sym2_ne hxy hzw hne
      have hcenter :
          r = (branchIndexedFan M hmax a).center :=
        (branchIndexedFan M hmax a).arm_support_inter_support hea heb he_ne r hra hrb
      rcases ha_endpoint with hax | hay
      · rw [hax] at hcenter
        exact hrP.2.1 hcenter
      · rw [hay] at hcenter
        exact hrP.2.2 hcenter
    · have hdisj := M.pairwise_disjoint hab
      change Disjoint (M.branchSet a) (M.branchSet b) at hdisj
      rw [Set.disjoint_left] at hdisj
      exact hdisj
        ((branchIndexedFan M hmax a).arm_support_subset _ hea r hra)
        ((branchIndexedFan M hmax b).arm_support_subset _ heb r hrb)

private noncomputable def minorModel_to_topologicalModel {V : Type u} {W : Type v}
    {X : SimpleGraph W} {G : SimpleGraph V} [Fintype W] [DecidableRel X.Adj]
    (M : Model X G) (hmax : X.maxDegree ≤ 3) :
    TopologicalModel X G := by
  classical
  exact {
    vertexMap := {
      toFun := fun x => (branchIndexedFan M hmax x).center
      inj' := branchIndexedFan_center_injective M hmax
    }
    edgePath := fun _ _ hxy => modelEdgePathBypass M hmax hxy
    edgePath_isPath := fun _ _ hxy => modelEdgePathBypass_isPath M hmax hxy
    inner_disjoint := fun _ _ _ _ hxy hzw hne =>
      modelEdgePathBypass_inner_disjoint M hmax hxy hzw hne
    branch_not_inner := fun _ _ _ hxy hinner =>
      modelEdgePathBypass_branch_not_inner M hmax hxy hinner
  }

theorem isTopologicalMinor_of_isMinor_of_maxDegree_le_three {V : Type u} {W : Type v}
    (X : SimpleGraph W) (G : SimpleGraph V)
    [Fintype W] [DecidableRel X.Adj] :
    X.maxDegree ≤ 3 → IsMinor X G → IsTopologicalMinor X G := by
  intro hmax hminor
  rcases hminor with ⟨M⟩
  exact ⟨minorModel_to_topologicalModel M hmax⟩

end Chapter01
end Diestel
