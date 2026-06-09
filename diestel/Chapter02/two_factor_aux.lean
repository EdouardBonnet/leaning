import Chapter01.theorem_1_8_1
import Chapter02.corollary_2_1_3
import Mathlib.Data.List.Rotate

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

namespace TwoFactorAux

variable {V : Type u} (G : SimpleGraph V)

lemma connectedComponent_toSimpleGraph_eulerian_of_even_regular
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (hreg : G.IsRegularOfDegree (2 * k)) (C : G.ConnectedComponent) :
    Diestel.Chapter01.IsEulerian C.toSimpleGraph := by
  letI : DecidablePred (fun x : V => x ∈ C.supp) := Classical.decPred _
  letI : Fintype C := Subtype.fintype (fun x : V => x ∈ C.supp)
  letI : DecidableRel C.toSimpleGraph.Adj := by
    dsimp [SimpleGraph.ConnectedComponent.toSimpleGraph, SimpleGraph.induce]
    infer_instance
  have hdegree : ∀ v : C, C.toSimpleGraph.degree v = G.degree v := by
    intro v
    exact SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := C.supp) (v := v) (by
      intro w hw
      exact (C.mem_supp_congr_adj hw).mp v.2)
  have heven : ∀ v : C, Even (C.toSimpleGraph.degree v) := by
    intro v
    rw [hdegree v, hreg.degree_eq v.1]
    exact ⟨k, by omega⟩
  exact ((Diestel.Chapter01.theorem_1_8_1 C.toSimpleGraph)
    C.connected_toSimpleGraph).mpr heven

private lemma List.countP_dropLast_eq_tail_of_head_eq_getLast {α : Type u}
    (l : List α) (p : α → Bool) (hl : l ≠ [])
    (h : l.head hl = l.getLast hl) :
    l.dropLast.countP p = l.tail.countP p :=
  (List.IsRotated.dropLast_tail hl h).perm.countP_eq p

private lemma List.countP_or_eq_add_of_disjoint {α : Type u}
    (l : List α) (p q : α → Bool)
    (hdisj : ∀ x ∈ l, p x = true → q x = true → False) :
    l.countP (fun x => p x || q x) = l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, p y = true → q y = true → False := by
        intro y hy
        exact hdisj y (by simp [hy])
      by_cases hp : p x = true <;> by_cases hq : q x = true
      · exact (hdisj x (by simp) hp hq).elim
      · simp [hp, hq, ih htail]
        omega
      · simp [hp, hq, ih htail]
        omega
      · simp [hp, hq, ih htail]

lemma closedWalk_count_fst_darts_eq_count_snd_darts [DecidableEq V]
    {a : V} (p : G.Walk a a) (v : V) :
    p.darts.countP (fun d => d.fst = v) =
      p.darts.countP (fun d => d.snd = v) := by
  classical
  calc
    p.darts.countP (fun d => d.fst = v) =
        (p.darts.map (fun d => d.fst)).countP (fun x => x = v) := by
      exact (List.countP_map (p := fun x : V => x = v)
        (f := fun d : G.Dart => d.fst) (l := p.darts)).symm
    _ = p.support.dropLast.countP (fun x => x = v) := by
      rw [p.map_fst_darts]
    _ = p.support.tail.countP (fun x => x = v) := by
      exact List.countP_dropLast_eq_tail_of_head_eq_getLast p.support (fun x => x = v)
        p.support_ne_nil (by simp)
    _ = (p.darts.map (fun d => d.snd)).countP (fun x => x = v) := by
      rw [p.map_snd_darts]
    _ = p.darts.countP (fun d => d.snd = v) := by
      exact List.countP_map (p := fun x : V => x = v)
        (f := fun d : G.Dart => d.snd) (l := p.darts)

lemma eulerian_count_incident_edges_eq_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a : V} {p : G.Walk a a} (hp : p.IsEulerian)
    (v : V) :
    p.edges.countP (fun e => v ∈ e) = G.degree v := by
  classical
  have hfin :
      hp.isTrail.edgesFinset.filter (fun e : Sym2 V => v ∈ e) =
        G.incidenceFinset v := by
    ext e
    constructor
    · intro he
      have he' := Finset.mem_filter.mp he
      rw [SimpleGraph.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_edgeFinset).mpr (p.edges_subset_edgeSet he'.1), he'.2⟩
    · intro he
      rw [SimpleGraph.incidenceFinset_eq_filter] at he
      have he' := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr
        ⟨hp.mem_edges_iff.mpr ((SimpleGraph.mem_edgeFinset).mp he'.1), he'.2⟩
  rw [← SimpleGraph.card_incidenceFinset_eq_degree G v]
  rw [← hfin]
  rw [List.countP_eq_length_filter]
  rfl

lemma eulerian_count_out_add_in_eq_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a : V} {p : G.Walk a a} (hp : p.IsEulerian)
    (v : V) :
    p.darts.countP (fun d => d.fst = v) +
      p.darts.countP (fun d => d.snd = v) = G.degree v := by
  classical
  have hmap :
      p.edges.countP (fun e => v ∈ e) =
        p.darts.countP (fun d => v ∈ d.edge) := by
    exact List.countP_map (p := fun e : Sym2 V => v ∈ e)
      (f := SimpleGraph.Dart.edge) (l := p.darts)
  have hor :
      p.darts.countP (fun d => v ∈ d.edge) =
        p.darts.countP (fun d => d.fst = v || d.snd = v) := by
    apply List.countP_congr
    intro d _hd
    rw [decide_eq_true_iff]
    cases d with
    | mk p h =>
        cases p with
        | mk x y =>
            change v ∈ s(x, y) ↔ (decide (x = v) || decide (y = v)) = true
            rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
            rw [Sym2.mem_iff]
            tauto
  have hsplit :
      p.darts.countP (fun d => d.fst = v || d.snd = v) =
        p.darts.countP (fun d => d.fst = v) +
          p.darts.countP (fun d => d.snd = v) := by
    exact List.countP_or_eq_add_of_disjoint p.darts
      (fun d => d.fst = v) (fun d => d.snd = v) (by
        intro d _hd hfst hsnd
        exact d.fst_ne_snd ((of_decide_eq_true hfst).trans (of_decide_eq_true hsnd).symm))
  rw [← eulerian_count_incident_edges_eq_degree G hp v]
  rw [hmap, hor, hsplit]

lemma eulerian_count_out_eq_half_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a : V} {p : G.Walk a a} (hp : p.IsEulerian)
    {k : ℕ} (hdeg : G.degree v = 2 * k) :
    p.darts.countP (fun d => d.fst = v) = k := by
  classical
  have hbal := closedWalk_count_fst_darts_eq_count_snd_darts G p v
  have hsum := eulerian_count_out_add_in_eq_degree G hp v
  omega

lemma eulerian_count_in_eq_half_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {a : V} {p : G.Walk a a} (hp : p.IsEulerian)
    {k : ℕ} (hdeg : G.degree v = 2 * k) :
    p.darts.countP (fun d => d.snd = v) = k := by
  classical
  rw [← closedWalk_count_fst_darts_eq_count_snd_darts G p v]
  exact eulerian_count_out_eq_half_degree G hp hdeg

private lemma nat_card_subtype_mem_list_and {α : Type u} [DecidableEq α]
    (l : List α) (hnd : l.Nodup) (p : α → Prop) [DecidablePred p] :
    Nat.card {x : α // x ∈ l ∧ p x} = l.countP p := by
  classical
  let s : Finset α := l.toFinset.filter p
  have hs : s = (l.filter p).toFinset := by
    ext x
    simp [s]
  have hs_card : s.card = (l.filter p).length := by
    rw [hs, List.toFinset_card_of_nodup (hnd.filter p)]
  have hmem : ∀ x : α, x ∈ s ↔ x ∈ l ∧ p x := by
    intro x
    simp [s]
  calc
    Nat.card {x : α // x ∈ l ∧ p x} =
        @Fintype.card {x : α // x ∈ l ∧ p x} (Fintype.ofFinset s hmem) := by
      exact @Nat.card_eq_fintype_card {x : α // x ∈ l ∧ p x} (Fintype.ofFinset s hmem)
    _ = s.card := Fintype.card_ofFinset s hmem
    _ = (l.filter p).length := hs_card
    _ = l.countP p := List.countP_eq_length_filter.symm

private noncomputable def dartTargetEquiv [DecidableEq V] (l : List G.Dart) (v : V) :
    {d : G.Dart // d ∈ l ∧ d.fst = v} ≃
      {w : V // ∃ d : G.Dart, d ∈ l ∧ d.fst = v ∧ d.snd = w} where
  toFun d := ⟨d.1.snd, d.1, d.2.1, d.2.2, rfl⟩
  invFun w := by
    classical
    exact ⟨Classical.choose w.2,
      (Classical.choose_spec w.2).1,
      (Classical.choose_spec w.2).2.1⟩
  left_inv d := by
    classical
    apply Subtype.ext
    have hspec := Classical.choose_spec
      (show ∃ d' : G.Dart, d' ∈ l ∧ d'.fst = v ∧ d'.snd = d.1.snd from
        ⟨d.1, d.2.1, d.2.2, rfl⟩)
    apply SimpleGraph.Dart.ext
    ext
    · exact hspec.2.1.trans d.2.2.symm
    · exact hspec.2.2
  right_inv w := by
    classical
    apply Subtype.ext
    exact (Classical.choose_spec w.2).2.2

lemma natCard_dart_targets_eq_countP [DecidableEq V]
    (l : List G.Dart) (hedges : (l.map SimpleGraph.Dart.edge).Nodup) (v : V) :
    Nat.card {w : V // ∃ d : G.Dart, d ∈ l ∧ d.fst = v ∧ d.snd = w} =
      l.countP (fun d => d.fst = v) := by
  classical
  have hnd : l.Nodup := hedges.of_map SimpleGraph.Dart.edge
  rw [← nat_card_subtype_mem_list_and l hnd (fun d : G.Dart => d.fst = v)]
  exact Nat.card_congr (dartTargetEquiv (G := G) l v).symm

private noncomputable def dartSourceEquiv [DecidableEq V] (l : List G.Dart) (v : V) :
    {d : G.Dart // d ∈ l ∧ d.snd = v} ≃
      {w : V // ∃ d : G.Dart, d ∈ l ∧ d.snd = v ∧ d.fst = w} where
  toFun d := ⟨d.1.fst, d.1, d.2.1, d.2.2, rfl⟩
  invFun w := by
    classical
    exact ⟨Classical.choose w.2,
      (Classical.choose_spec w.2).1,
      (Classical.choose_spec w.2).2.1⟩
  left_inv d := by
    classical
    apply Subtype.ext
    have hspec := Classical.choose_spec
      (show ∃ d' : G.Dart, d' ∈ l ∧ d'.snd = v ∧ d'.fst = d.1.fst from
        ⟨d.1, d.2.1, d.2.2, rfl⟩)
    apply SimpleGraph.Dart.ext
    ext
    · exact hspec.2.2
    · exact hspec.2.1.trans d.2.2.symm
  right_inv w := by
    classical
    apply Subtype.ext
    exact (Classical.choose_spec w.2).2.2

lemma natCard_dart_sources_eq_countP [DecidableEq V]
    (l : List G.Dart) (hedges : (l.map SimpleGraph.Dart.edge).Nodup) (v : V) :
    Nat.card {w : V // ∃ d : G.Dart, d ∈ l ∧ d.snd = v ∧ d.fst = w} =
      l.countP (fun d => d.snd = v) := by
  classical
  have hnd : l.Nodup := hedges.of_map SimpleGraph.Dart.edge
  rw [← nat_card_subtype_mem_list_and l hnd (fun d : G.Dart => d.snd = v)]
  exact Nat.card_congr (dartSourceEquiv (G := G) l v).symm

def liftComponentDart {G : SimpleGraph V} (C : G.ConnectedComponent)
    (d : C.toSimpleGraph.Dart) : G.Dart :=
  ⟨(d.fst.1, d.snd.1), by
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph, SimpleGraph.induce] using d.adj⟩

lemma componentDart_edge_eq_of_lift_edge_eq {G : SimpleGraph V}
    (C : G.ConnectedComponent) {d₁ d₂ : C.toSimpleGraph.Dart}
    (h : (liftComponentDart C d₁).edge = (liftComponentDart C d₂).edge) :
    d₁.edge = d₂.edge := by
  cases d₁ with
  | mk p1 h1 =>
  cases d₂ with
  | mk p2 h2 =>
    cases p1 with
    | mk a1 b1 =>
    cases p2 with
    | mk a2 b2 =>
      simp [liftComponentDart, SimpleGraph.Dart.edge] at h ⊢
      exact h

lemma liftedDartList_edges_nodup {G : SimpleGraph V} [DecidableEq V]
    (C : G.ConnectedComponent) {a : C}
    (p : C.toSimpleGraph.Walk a a) (hp : p.IsEulerian) :
    ((p.darts.map (liftComponentDart C)).map SimpleGraph.Dart.edge).Nodup := by
  rw [List.map_map]
  have hdarts : p.darts.Nodup := hp.isTrail.edges_nodup.of_map SimpleGraph.Dart.edge
  apply hdarts.map_on
  intro d₁ hd₁ d₂ hd₂ h
  exact List.inj_on_of_nodup_map hp.isTrail.edges_nodup hd₁ hd₂
    (componentDart_edge_eq_of_lift_edge_eq C h)

lemma liftedDarts_countP_fst {G : SimpleGraph V} [DecidableEq V]
    (C : G.ConnectedComponent) {a : C}
    (p : C.toSimpleGraph.Walk a a) (v : C) :
    (p.darts.map (liftComponentDart C)).countP (fun d => d.fst = v.1) =
      p.darts.countP (fun d => d.fst = v) := by
  rw [List.countP_map]
  apply List.countP_congr
  intro d _hd
  change decide ((liftComponentDart C d).fst = v.1) = true ↔
    decide (d.fst = v) = true
  rw [decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

lemma liftedDarts_countP_snd {G : SimpleGraph V} [DecidableEq V]
    (C : G.ConnectedComponent) {a : C}
    (p : C.toSimpleGraph.Walk a a) (v : C) :
    (p.darts.map (liftComponentDart C)).countP (fun d => d.snd = v.1) =
      p.darts.countP (fun d => d.snd = v) := by
  rw [List.countP_map]
  apply List.countP_congr
  intro d _hd
  change decide ((liftComponentDart C d).snd = v.1) = true ↔
    decide (d.snd = v) = true
  rw [decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

/-- The left side of Mathlib's bipartite double cover. -/
def doubleLeftSide : Set (V ⊕ V) :=
  {x | x.isLeft}

/-- The right side of Mathlib's bipartite double cover. -/
def doubleRightSide : Set (V ⊕ V) :=
  {x | x.isRight}

private noncomputable def leftNeighborEquiv [DecidableRel G.Adj] (v : V) :
    (G.bipartiteDoubleCover.neighborSet (Sum.inl v)) ≃ G.neighborSet v where
  toFun x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · simp at hx
    · exact ⟨x, hx⟩
  invFun x := ⟨Sum.inr x.1, x.2⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · simp at hx
    · rfl
  right_inv x := rfl

private noncomputable def rightNeighborEquiv [DecidableRel G.Adj] (v : V) :
    (G.bipartiteDoubleCover.neighborSet (Sum.inr v)) ≃ G.neighborSet v where
  toFun x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · exact ⟨x, hx⟩
    · simp at hx
  invFun x := ⟨Sum.inl x.1, x.2⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · rfl
    · simp at hx
  right_inv x := rfl

lemma bipartiteDoubleCover_degree_inl [Fintype V] [DecidableRel G.Adj] (v : V) :
    G.bipartiteDoubleCover.degree (Sum.inl v) = G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (leftNeighborEquiv G v)

lemma bipartiteDoubleCover_degree_inr [Fintype V] [DecidableRel G.Adj] (v : V) :
    G.bipartiteDoubleCover.degree (Sum.inr v) = G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (rightNeighborEquiv G v)

lemma bipartiteDoubleCover_regular [Fintype V] [DecidableRel G.Adj] {d : ℕ}
    (hreg : G.IsRegularOfDegree d) :
    G.bipartiteDoubleCover.IsRegularOfDegree d := by
  intro x
  rcases x with v | v
  · rw [bipartiteDoubleCover_degree_inl G v, hreg.degree_eq v]
  · rw [bipartiteDoubleCover_degree_inr G v, hreg.degree_eq v]

lemma exists_isPerfectMatching_bipartiteDoubleCover [Fintype V] [DecidableRel G.Adj]
    {d : ℕ} (hd : 1 ≤ d) (hreg : G.IsRegularOfDegree d) :
    ∃ M : G.bipartiteDoubleCover.Subgraph, M.IsPerfectMatching := by
  classical
  exact corollary_2_1_3 G.bipartiteDoubleCover
    (doubleLeftSide (V := V)) (doubleRightSide (V := V)) d
    SimpleGraph.isBipartiteWith_bipartiteDoubleCover
    (bipartiteDoubleCover_regular G hreg) hd

/--
The simple graph obtained from a directed permutation `e`: keep the
undirected edge `{x, y}` when either `e x = y` or `e y = x`.
-/
def permutationFactorGraph (e : V ≃ V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (e x = y ∨ e y = x)
  symm := by
    rintro x y ⟨hxy, hdir⟩
    exact ⟨hxy.symm, hdir.symm⟩
  loopless := ⟨fun x h => h.1.ne rfl⟩

lemma permutationFactorGraph_le (e : V ≃ V) :
    permutationFactorGraph G e ≤ G := by
  intro x y hxy
  exact hxy.1

lemma permutationFactorGraph_neighborSet_eq (e : V ≃ V)
    (hadj : ∀ v : V, G.Adj v (e v)) (hno_two_cycle : ∀ v : V, e (e v) ≠ v)
    (v : V) :
    (permutationFactorGraph G e).neighborSet v = ({e v, e.symm v} : Set V) := by
  ext y
  constructor
  · intro hy
    rcases hy.2 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by simpa using congrArg e.symm h)
  · intro hy
    rcases hy with hy | hy
    · rw [hy]
      exact ⟨hadj v, Or.inl rfl⟩
    · rw [hy]
      exact ⟨by simpa using (hadj (e.symm v)).symm, Or.inr (by simp)⟩

lemma permutationFactorGraph_degree_two [Fintype V] (e : V ≃ V)
    (hadj : ∀ v : V, G.Adj v (e v)) (hno_two_cycle : ∀ v : V, e (e v) ≠ v)
    (v : V) :
    Nat.card ((permutationFactorGraph G e).neighborSet v) = 2 := by
  classical
  have hne : e v ≠ e.symm v := by
    intro h
    exact hno_two_cycle v (by simpa [h])
  rw [permutationFactorGraph_neighborSet_eq G e hadj hno_two_cycle v]
  simp [hne]

lemma hasKFactor_two_of_permutation [Fintype V] [DecidableRel G.Adj] (e : V ≃ V)
    (hadj : ∀ v : V, G.Adj v (e v)) (hno_two_cycle : ∀ v : V, e (e v) ≠ v) :
    HasKFactor G 2 := by
  exact ⟨permutationFactorGraph G e, permutationFactorGraph_le G e,
    permutationFactorGraph_degree_two G e hadj hno_two_cycle⟩

lemma hasKFactor_two_of_bijective_function [Fintype V] [DecidableRel G.Adj]
    (f : V → V) (hbij : Function.Bijective f)
    (hadj : ∀ v : V, G.Adj v (f v)) (hno_two_cycle : ∀ v : V, f (f v) ≠ v) :
    HasKFactor G 2 := by
  let e : V ≃ V := Equiv.ofBijective f hbij
  exact hasKFactor_two_of_permutation G e hadj hno_two_cycle

/-- The bipartite graph associated to an oriented relation on `V`. -/
def orientedDoubleCover (R : V → V → Prop) : SimpleGraph (V ⊕ V) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inr b => R a b
    | Sum.inr b, Sum.inl a => R a b
    | _, _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> simpa using h
  loopless := ⟨fun x => by cases x <;> simp⟩

instance orientedDoubleCover_decidableRel (R : V → V → Prop) [DecidableRel R] :
    DecidableRel (orientedDoubleCover R).Adj := by
  intro x y
  cases x <;> cases y <;> simp [orientedDoubleCover] <;> infer_instance

lemma orientedDoubleCover_isBipartiteWith (R : V → V → Prop) :
    (orientedDoubleCover R).IsBipartiteWith
      (doubleLeftSide (V := V)) (doubleRightSide (V := V)) where
  disjoint := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    cases x <;> simp [doubleLeftSide, doubleRightSide] at hx hy
  mem_of_adj := by
    intro x y hxy
    cases x <;> cases y <;>
      simp [orientedDoubleCover, doubleLeftSide, doubleRightSide] at hxy ⊢

private noncomputable def orientedLeftNeighborEquiv (R : V → V → Prop) (v : V) :
    ((orientedDoubleCover R).neighborSet (Sum.inl v)) ≃ {w : V // R v w} where
  toFun x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · simp [orientedDoubleCover] at hx
    · exact ⟨x, hx⟩
  invFun x := ⟨Sum.inr x.1, x.2⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · simp [orientedDoubleCover] at hx
    · rfl
  right_inv x := rfl

private noncomputable def orientedRightNeighborEquiv (R : V → V → Prop) (v : V) :
    ((orientedDoubleCover R).neighborSet (Sum.inr v)) ≃ {w : V // R w v} where
  toFun x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · exact ⟨x, hx⟩
    · simp [orientedDoubleCover] at hx
  invFun x := ⟨Sum.inl x.1, x.2⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rcases x with x | x
    · rfl
    · simp [orientedDoubleCover] at hx
  right_inv x := rfl

lemma orientedDoubleCover_degree_inl [Fintype V] [DecidableRel R] {k : ℕ}
    (hout : Nat.card {w : V // R v w} = k) :
    (orientedDoubleCover R).degree (Sum.inl v) = k := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [← hout, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (orientedLeftNeighborEquiv R v)

lemma orientedDoubleCover_degree_inr [Fintype V] [DecidableRel R] {k : ℕ}
    (hin : Nat.card {w : V // R w v} = k) :
    (orientedDoubleCover R).degree (Sum.inr v) = k := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [← hin, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (orientedRightNeighborEquiv R v)

lemma orientedDoubleCover_regular [Fintype V] [DecidableRel R] {k : ℕ}
    (hout : ∀ v : V, Nat.card {w : V // R v w} = k)
    (hin : ∀ v : V, Nat.card {w : V // R w v} = k) :
    (orientedDoubleCover R).IsRegularOfDegree k := by
  intro x
  rcases x with v | v
  · exact orientedDoubleCover_degree_inl (R := R) (v := v) (hout v)
  · exact orientedDoubleCover_degree_inr (R := R) (v := v) (hin v)

private noncomputable def perfectMatchingRightMate {R : V → V → Prop}
    {M : (orientedDoubleCover R).Subgraph} (hM : M.IsPerfectMatching) (v : V) : V :=
  Classical.choose <| by
    let w := Classical.choose (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inl v))
    have hw : M.Adj (Sum.inl v) w :=
      (Classical.choose_spec
        (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inl v))).1
    rcases w with w | w
    · have hbad : (orientedDoubleCover R).Adj (Sum.inl v) (Sum.inl w) := M.adj_sub hw
      simp [orientedDoubleCover] at hbad
    · exact ⟨w, by simpa using hw⟩

private lemma perfectMatchingRightMate_adj {R : V → V → Prop}
    {M : (orientedDoubleCover R).Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    M.Adj (Sum.inl v) (Sum.inr (perfectMatchingRightMate hM v)) :=
  Classical.choose_spec <| by
    let w := Classical.choose (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inl v))
    have hw : M.Adj (Sum.inl v) w :=
      (Classical.choose_spec
        (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inl v))).1
    rcases w with w | w
    · have hbad : (orientedDoubleCover R).Adj (Sum.inl v) (Sum.inl w) := M.adj_sub hw
      simp [orientedDoubleCover] at hbad
    · exact ⟨w, by simpa using hw⟩

private lemma perfectMatchingRightMate_rel {R : V → V → Prop}
    {M : (orientedDoubleCover R).Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    R v (perfectMatchingRightMate hM v) := by
  have hAdj : (orientedDoubleCover R).Adj (Sum.inl v) (Sum.inr (perfectMatchingRightMate hM v)) :=
    M.adj_sub (perfectMatchingRightMate_adj hM v)
  simpa [orientedDoubleCover] using hAdj

lemma hasKFactor_two_of_regular_orientation [Fintype V] [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] {k : ℕ} (hk : 1 ≤ k)
    (hsub : ∀ {x y : V}, R x y → G.Adj x y)
    (hasymm : ∀ {x y : V}, R x y → ¬ R y x)
    (hout : ∀ v : V, Nat.card {w : V // R v w} = k)
    (hin : ∀ v : V, Nat.card {w : V // R w v} = k) :
    HasKFactor G 2 := by
  classical
  obtain ⟨M, hM⟩ := corollary_2_1_3 (orientedDoubleCover R)
    (doubleLeftSide (V := V)) (doubleRightSide (V := V)) k
    (orientedDoubleCover_isBipartiteWith R)
    (orientedDoubleCover_regular (R := R) hout hin) hk
  let f : V → V := fun v => perfectMatchingRightMate hM v
  have hf_rel : ∀ v : V, R v (f v) := by
    intro v
    exact perfectMatchingRightMate_rel hM v
  have hf_adj : ∀ v : V, G.Adj v (f v) := fun v => hsub (hf_rel v)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hx : M.Adj (Sum.inl x) (Sum.inr (f x)) := perfectMatchingRightMate_adj hM x
    have hy : M.Adj (Sum.inl y) (Sum.inr (f x)) := by
      simpa [f, hxy] using perfectMatchingRightMate_adj hM y
    have hsum : Sum.inl x = Sum.inl y := hM.1.eq_of_adj_right hx hy
    simpa using hsum
  have hf_surj : Function.Surjective f := by
    intro y
    let z := Classical.choose (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inr y))
    have hz : M.Adj (Sum.inr y) z :=
      (Classical.choose_spec
        (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inr y))).1
    have hz_left : ∃ x : V, M.Adj (Sum.inl x) (Sum.inr y) := by
      rcases z with z | z
      · exact ⟨z, M.symm hz⟩
      · have hbad : (orientedDoubleCover R).Adj (Sum.inr y) (Sum.inr z) := M.adj_sub hz
        simp [orientedDoubleCover] at hbad
    rcases hz_left with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hx' : M.Adj (Sum.inl x) (Sum.inr (f x)) := perfectMatchingRightMate_adj hM x
    have hsum : Sum.inr y = Sum.inr (f x) :=
      (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM (Sum.inl x)).unique hx hx'
    simpa using hsum.symm
  have hf_no_two : ∀ v : V, f (f v) ≠ v := by
    intro v hcycle
    exact hasymm (hf_rel v) (by simpa [f, hcycle] using hf_rel (f v))
  exact hasKFactor_two_of_bijective_function G f ⟨hf_inj, hf_surj⟩ hf_adj hf_no_two

end TwoFactorAux

end Chapter02
end Diestel
