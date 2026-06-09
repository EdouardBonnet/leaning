import Chapter01.definitions_ch1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Trails

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

def leNatSubtypeEquivFin (r : ℕ) : {n : ℕ // n ≤ r} ≃ Fin (r + 1) where
  toFun n := ⟨n.1, Nat.lt_succ_of_le n.2⟩
  invFun i := ⟨i.1, Nat.le_of_lt_succ i.2⟩
  left_inv n := by
    ext
    rfl
  right_inv i := by
    ext
    rfl

private lemma isCycle_isTrail {V : Type u} {G : SimpleGraph V} {a : V}
    {c : G.Walk a a} (hc : c.IsCycle) : c.IsTrail := by
  cases c with
  | nil =>
      simp [SimpleGraph.Walk.isTrail_def]
  | cons h p =>
      rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
      rw [SimpleGraph.Walk.isTrail_cons]
      exact ⟨hc.1.isTrail, hc.2⟩

theorem cycle_length_ge_of_egirth_ge {V : Type u} {G : SimpleGraph V}
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {a : V} {c : G.Walk a a}
    (hc : c.IsCycle) :
    g ≤ c.length := by
  have hle : (g : ℕ∞) ≤ (c.length : ℕ∞) :=
    hg.trans (SimpleGraph.egirth_le_length hc)
  exact ENat.coe_le_coe.mp hle

theorem egirth_bound_of_two_distinct_paths {V : Type u} {G : SimpleGraph V}
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {x y : V}
    {p q : G.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hne : (⟨p, hp⟩ : G.Path x y) ≠ ⟨q, hq⟩) :
    g ≤ p.length + q.length := by
  classical
  let E : Finset (Sym2 V) := p.edges.toFinset ∪ q.edges.toFinset
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  have hH_finite : H.edgeSet.Finite :=
    (Set.Finite.ofFinset E (by intro e; rfl)).subset (by
      intro e he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at he
      exact he.1)
  letI : Fintype H.edgeSet := hH_finite.fintype
  have hp_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr he))
    · exact SimpleGraph.not_isDiag_of_mem_edgeSet G (p.edges_subset_edgeSet he)
  have hq_edges : ∀ e ∈ q.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr he))
    · exact SimpleGraph.not_isDiag_of_mem_edgeSet G (q.edges_subset_edgeSet he)
  let pH : H.Walk x y := p.transfer H hp_edges
  let qH : H.Walk x y := q.transfer H hq_edges
  have hpH : pH.IsPath := hp.transfer hp_edges
  have hqH : qH.IsPath := hq.transfer hq_edges
  have hpaths_ne : (⟨pH, hpH⟩ : H.Path x y) ≠ ⟨qH, hqH⟩ := by
    intro hEq
    apply hne
    apply Subtype.ext
    have hWalkEq := congrArg (fun r : H.Path x y => r.1) hEq
    apply SimpleGraph.Walk.ext_support
    have hsupport := congrArg (fun w : H.Walk x y => w.support) hWalkEq
    dsimp [pH, qH] at hsupport
    rw [SimpleGraph.Walk.support_transfer, SimpleGraph.Walk.support_transfer] at hsupport
    exact hsupport
  have hnot_acyclic : ¬ H.IsAcyclic := by
    intro hacy
    exact hpaths_ne (hacy.path_unique ⟨pH, hpH⟩ ⟨qH, hqH⟩)
  obtain ⟨z, cH, hcH, _hgirthH⟩ :=
    (SimpleGraph.exists_girth_eq_length (G := H)).mpr hnot_acyclic
  have hH_le_G : H ≤ G := by
    rw [SimpleGraph.fromEdgeSet_le]
    intro e he
    rcases Finset.mem_union.mp he.1 with heP | heQ
    · exact p.edges_subset_edgeSet (List.mem_toFinset.mp heP)
    · exact q.edges_subset_edgeSet (List.mem_toFinset.mp heQ)
  have hcH_trail : cH.IsTrail := isCycle_isTrail hcH
  have hcycle_bound : cH.length ≤ p.length + q.length := by
    have h1 := hcH_trail.length_le_card_edgeFinset
    have hcard_to_union : H.edgeFinset.card ≤ E.card := by
      apply Finset.card_le_card
      intro e he
      have heH : e ∈ H.edgeSet := (SimpleGraph.mem_edgeFinset).mp he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at heH
      exact heH.1
    have hcard_union :
        E.card ≤ p.edges.toFinset.card + q.edges.toFinset.card := by
      dsimp [E]
      exact Finset.card_union_le p.edges.toFinset q.edges.toFinset
    have hp_card : p.edges.toFinset.card ≤ p.length := by
      simpa [SimpleGraph.Walk.length_edges] using List.toFinset_card_le p.edges
    have hq_card : q.edges.toFinset.card ≤ q.length := by
      simpa [SimpleGraph.Walk.length_edges] using List.toFinset_card_le q.edges
    omega
  have hc_edges : ∀ e ∈ cH.edges, e ∈ G.edgeSet := by
    intro e he
    exact SimpleGraph.edgeSet_mono hH_le_G (cH.edges_subset_edgeSet he)
  have hcG : (cH.transfer G hc_edges).IsCycle := hcH.transfer hc_edges
  have hg_le : g ≤ cH.length := by
    simpa using cycle_length_ge_of_egirth_ge hg hcG
  omega

theorem egirth_bound_of_two_paths_length_lt {V : Type u} {G : SimpleGraph V}
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {x y : V}
    {p q : G.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : q.length < p.length) :
    g ≤ p.length + q.length :=
  egirth_bound_of_two_distinct_paths hg hp hq (by
    intro hEq
    have hLen := congrArg (fun r : G.Path x y => r.1.length) hEq
    dsimp at hLen
    omega)

theorem path_eq_of_length_sum_lt_egirth {V : Type u} {G : SimpleGraph V}
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {x y : V}
    {p q : G.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < g) :
    (⟨p, hp⟩ : G.Path x y) = ⟨q, hq⟩ := by
  by_contra hne
  have hge := egirth_bound_of_two_distinct_paths hg hp hq hne
  omega

theorem idxOf_getVert_of_isPath {V : Type u} {G : SimpleGraph V} {a b : V}
    [DecidableEq V] {p : G.Walk a b} (hp : p.IsPath) {i : ℕ}
    (hi : i ≤ p.length) :
    List.idxOf (p.getVert i) p.support = i := by
  have hnodup : p.support.Nodup := hp.support_nodup
  have hidx_lt : i < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hget : p.getVert i = p.support[i] := by
    exact SimpleGraph.Walk.getVert_eq_support_getElem p hi
  rw [hget]
  exact List.idxOf_getElem hnodup i hidx_lt

theorem concat_isPath_of_not_mem {V : Type u} {G : SimpleGraph V} {a b c : V}
    {p : G.Walk a b} (hp : p.IsPath) (hbc : G.Adj b c) (hc : c ∉ p.support) :
    (p.concat hbc).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  rw [SimpleGraph.Walk.support_concat]
  simpa [List.concat_eq_append] using hp.support_nodup.concat hc

theorem support_not_mem_of_short_concat {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {z x y : V} {p : G.Walk z x} (hp : p.IsPath) (hxy : G.Adj x y)
    (hshort : p.length + 1 < g)
    (hnot_prev : p.length = 0 ∨ y ≠ p.getVert (p.length - 1)) :
    y ∉ p.support := by
  intro hy
  have hy_ne_x : y ≠ x := hxy.ne.symm
  have hidx_lt_len : List.idxOf y p.support < p.support.length := by
    exact List.idxOf_lt_length_iff.mpr hy
  have hidx_le : List.idxOf y p.support ≤ p.length := by
    rw [SimpleGraph.Walk.length_support] at hidx_lt_len
    omega
  have hidx_ne_len : List.idxOf y p.support ≠ p.length := by
    intro hidx
    have hget : y = p.getVert p.length := by
      calc
        y = p.support[List.idxOf y p.support] := by
          exact (List.getElem_idxOf hidx_lt_len).symm
        _ = p.support[p.length] := by
          congr
        _ = p.getVert p.length := by
          exact (SimpleGraph.Walk.getVert_eq_support_getElem p le_rfl).symm
    exact hy_ne_x (by simpa [SimpleGraph.Walk.getVert_length] using hget)
  have hidx_ne_pred : p.length ≠ 0 → List.idxOf y p.support ≠ p.length - 1 := by
    intro hpos hidx
    rcases hnot_prev with hzero | hneq
    · exact hpos hzero
    · apply hneq
      have hle_pred : p.length - 1 ≤ p.length := by omega
      calc
        y = p.support[List.idxOf y p.support] := by
          exact (List.getElem_idxOf hidx_lt_len).symm
        _ = p.support[p.length - 1] := by
          congr
        _ = p.getVert (p.length - 1) := by
          exact (SimpleGraph.Walk.getVert_eq_support_getElem p hle_pred).symm
  have hseg_gt_one :
      1 < (p.dropUntil y hy).length := by
    rw [SimpleGraph.Walk.length_dropUntil]
    by_cases hlen0 : p.length = 0
    · have hidx0 : List.idxOf y p.support = 0 := by omega
      have hyx : y = x := by
        calc
          y = p.support[List.idxOf y p.support] := by
            exact (List.getElem_idxOf hidx_lt_len).symm
          _ = p.support[0] := by
            congr
          _ = p.getVert 0 := by
            exact (SimpleGraph.Walk.getVert_eq_support_getElem p (by omega)).symm
          _ = x := by
            rw [← hlen0, SimpleGraph.Walk.getVert_length]
      exact False.elim (hy_ne_x hyx)
    · have hidx_ne_pred' : List.idxOf y p.support ≠ p.length - 1 :=
        hidx_ne_pred hlen0
      omega
  let q : G.Walk y x := SimpleGraph.Walk.cons hxy.symm SimpleGraph.Walk.nil
  have hq_path : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    dsimp [q]
    simp [SimpleGraph.Walk.support_cons, hxy.ne']
  have hq_len : q.length = 1 := by
    dsimp [q]
  have hdrop_path : (p.dropUntil y hy).IsPath := hp.dropUntil hy
  have hcycle_bound :
      g ≤ (p.dropUntil y hy).length + q.length :=
    egirth_bound_of_two_paths_length_lt hg hdrop_path hq_path (by
      rw [hq_len]
      exact hseg_gt_one)
  have hdrop_len_le : (p.dropUntil y hy).length ≤ p.length := by
    rw [SimpleGraph.Walk.length_dropUntil]
    omega
  rw [hq_len] at hcycle_bound
  omega

theorem concat_isPath_of_girth_ge {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {z x y : V} {p : G.Walk z x} (hp : p.IsPath) (hxy : G.Adj x y)
    (hshort : p.length + 1 < g)
    (hnot_prev : p.length = 0 ∨ y ≠ p.getVert (p.length - 1)) :
    (p.concat hxy).IsPath :=
  concat_isPath_of_not_mem hp hxy
    (support_not_mem_of_short_concat hg hp hxy hshort hnot_prev)

/-- A walk is non-returning if it never immediately traverses an edge and then returns. -/
def IsNonreturning {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : Prop :=
  ∀ i : ℕ, i + 2 ≤ p.length → p.getVert i ≠ p.getVert (i + 2)

theorem isPath_of_isNonreturning_of_length_lt_girth {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {a b : V} (p : G.Walk a b) (hnr : IsNonreturning p) (hshort : p.length < g) :
    p.IsPath := by
  induction p with
  | nil =>
      exact SimpleGraph.Walk.IsPath.nil
  | cons h q ih =>
      rw [SimpleGraph.Walk.cons_isPath_iff]
      have hnrq : IsNonreturning q := by
        intro i hi
        have hneq := hnr (i + 1) (by
          rw [SimpleGraph.Walk.length_cons]
          omega)
        simpa [IsNonreturning, Nat.add_assoc] using hneq
      have hqshort : q.length < g := by
        rw [SimpleGraph.Walk.length_cons] at hshort
        omega
      have hq_path : q.IsPath := ih hnrq hqshort
      refine ⟨hq_path, ?_⟩
      by_cases hqnil : q.Nil
      · intro hu
        rw [SimpleGraph.Walk.nil_iff_support_eq.mp hqnil] at hu
        simp at hu
        exact h.ne hu
      · have hfirst : (SimpleGraph.Walk.cons h q).getVert 0 ≠ q.snd := by
          have hneq := hnr 0 (by
            rw [SimpleGraph.Walk.length_cons]
            have hqpos : 0 < q.length :=
              SimpleGraph.Walk.not_nil_iff_lt_length.mp hqnil
            omega)
          simpa [IsNonreturning] using hneq
        have hrev_pred :
            q.reverse.getVert (q.reverse.length - 1) = q.snd := by
          rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.getVert_reverse]
          have hcalc : q.length - (q.length - 1) = 1 := by
            have hqpos : 0 < q.length :=
              SimpleGraph.Walk.not_nil_iff_lt_length.mp hqnil
            omega
          rw [hcalc]
        have hnot_rev :=
          support_not_mem_of_short_concat hg hq_path.reverse h.symm
            (by
              rw [SimpleGraph.Walk.length_reverse]
              rw [SimpleGraph.Walk.length_cons] at hshort
              omega)
            (Or.inr (by
              rw [hrev_pred]
              simpa using hfirst))
        intro hu
        apply hnot_rev
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr hu

theorem exists_two_forward_neighbors {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) :
    ∃ t : Finset V, t ⊆ (G.neighborFinset x).erase pred ∧ t.card = 2 := by
  have hdegx : 3 ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
  have hpred_mem : pred ∈ G.neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hpred
  have hcard_erase :
      ((G.neighborFinset x).erase pred).card = (G.neighborFinset x).card - 1 :=
    Finset.card_erase_of_mem hpred_mem
  have hcard_neigh : (G.neighborFinset x).card = G.degree x :=
    SimpleGraph.card_neighborFinset_eq_degree G x
  have htwo : 2 ≤ ((G.neighborFinset x).erase pred).card := by
    omega
  exact Finset.exists_subset_card_eq htwo

noncomputable def twoForwardSet {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) : Finset V :=
  Classical.choose (exists_two_forward_neighbors G hmin hpred)

theorem twoForwardSet_spec {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) :
    twoForwardSet G hmin hpred ⊆ (G.neighborFinset x).erase pred ∧
      (twoForwardSet G hmin hpred).card = 2 :=
  Classical.choose_spec (exists_two_forward_neighbors G hmin hpred)

theorem twoForwardSet_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) :
    (twoForwardSet G hmin hpred).card = 2 :=
  (twoForwardSet_spec G hmin hpred).2

noncomputable def twoForwardEquiv {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) :
    Fin 2 ≃ twoForwardSet G hmin hpred :=
  (finCongr (twoForwardSet_card G hmin hpred).symm).trans
    (Finset.equivFin (twoForwardSet G hmin hpred)).symm

noncomputable def twoForwardVertex {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) (i : Fin 2) : V :=
  (twoForwardEquiv G hmin hpred i).1

theorem twoForwardVertex_injective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) :
    Function.Injective (twoForwardVertex G hmin hpred) := by
  intro i j hij
  apply (twoForwardEquiv G hmin hpred).injective
  exact Subtype.ext hij

theorem twoForwardVertex_adj {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) (i : Fin 2) :
    G.Adj x (twoForwardVertex G hmin hpred i) := by
  have hmem :
      twoForwardVertex G hmin hpred i ∈
        twoForwardSet G hmin hpred :=
    (twoForwardEquiv G hmin hpred i).2
  have herase :
      twoForwardVertex G hmin hpred i ∈
        (G.neighborFinset x).erase pred :=
    (twoForwardSet_spec G hmin hpred).1 hmem
  have hneigh :
      twoForwardVertex G hmin hpred i ∈ G.neighborFinset x :=
    (Finset.mem_erase.mp herase).2
  rwa [SimpleGraph.mem_neighborFinset] at hneigh

theorem twoForwardVertex_ne_pred {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {x pred : V} (hmin : 3 ≤ G.minDegree) (hpred : G.Adj x pred) (i : Fin 2) :
    twoForwardVertex G hmin hpred i ≠ pred := by
  have hmem :
      twoForwardVertex G hmin hpred i ∈
        twoForwardSet G hmin hpred :=
    (twoForwardEquiv G hmin hpred i).2
  have herase :
      twoForwardVertex G hmin hpred i ∈
        (G.neighborFinset x).erase pred :=
    (twoForwardSet_spec G hmin hpred).1 hmem
  exact (Finset.mem_erase.mp herase).1

theorem exists_d_forward_neighbors {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred) :
    ∃ t : Finset V, t ⊆ (G.neighborFinset x).erase pred ∧ t.card = d - 1 := by
  have hdegx : d ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
  have hpred_mem : pred ∈ G.neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hpred
  have hcard_erase :
      ((G.neighborFinset x).erase pred).card = (G.neighborFinset x).card - 1 :=
    Finset.card_erase_of_mem hpred_mem
  have hcard_neigh : (G.neighborFinset x).card = G.degree x :=
    SimpleGraph.card_neighborFinset_eq_degree G x
  have hle : d - 1 ≤ ((G.neighborFinset x).erase pred).card := by
    omega
  exact Finset.exists_subset_card_eq hle

noncomputable def dForwardSet {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred) :
    Finset V :=
  Classical.choose (exists_d_forward_neighbors G hmin hpred)

theorem dForwardSet_spec {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred) :
    dForwardSet G hmin hpred ⊆ (G.neighborFinset x).erase pred ∧
      (dForwardSet G hmin hpred).card = d - 1 :=
  Classical.choose_spec (exists_d_forward_neighbors G hmin hpred)

theorem dForwardSet_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred) :
    (dForwardSet G hmin hpred).card = d - 1 :=
  (dForwardSet_spec G hmin hpred).2

noncomputable def dForwardEquiv {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred) :
    Fin (d - 1) ≃ dForwardSet G hmin hpred :=
  (finCongr (dForwardSet_card G hmin hpred).symm).trans
    (Finset.equivFin (dForwardSet G hmin hpred)).symm

noncomputable def dForwardVertex {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred)
    (i : Fin (d - 1)) : V :=
  (dForwardEquiv G hmin hpred i).1

theorem dForwardVertex_injective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred) :
    Function.Injective (dForwardVertex G hmin hpred) := by
  intro i j hij
  apply (dForwardEquiv G hmin hpred).injective
  exact Subtype.ext hij

theorem dForwardVertex_adj {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred)
    (i : Fin (d - 1)) :
    G.Adj x (dForwardVertex G hmin hpred i) := by
  have hmem :
      dForwardVertex G hmin hpred i ∈
        dForwardSet G hmin hpred :=
    (dForwardEquiv G hmin hpred i).2
  have herase :
      dForwardVertex G hmin hpred i ∈
        (G.neighborFinset x).erase pred :=
    (dForwardSet_spec G hmin hpred).1 hmem
  have hneigh :
      dForwardVertex G hmin hpred i ∈ G.neighborFinset x :=
    (Finset.mem_erase.mp herase).2
  rwa [SimpleGraph.mem_neighborFinset] at hneigh

theorem dForwardVertex_ne_pred {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d : ℕ} {x pred : V} (hmin : d ≤ G.minDegree) (hpred : G.Adj x pred)
    (i : Fin (d - 1)) :
    dForwardVertex G hmin hpred i ≠ pred := by
  have hmem :
      dForwardVertex G hmin hpred i ∈
        dForwardSet G hmin hpred :=
    (dForwardEquiv G hmin hpred i).2
  have herase :
      dForwardVertex G hmin hpred i ∈
        (G.neighborFinset x).erase pred :=
    (dForwardSet_spec G hmin hpred).1 hmem
  exact (Finset.mem_erase.mp herase).1

abbrev PathOfLength {V : Type u} (G : SimpleGraph V) (z : V) (n : ℕ) :=
  Σ x : V, {p : G.Walk z x // p.IsPath ∧ p.length = n}

def pathLastPred {V : Type u} {G : SimpleGraph V} {z : V} {n : ℕ}
    (P : PathOfLength G z n) : V :=
  P.2.1.getVert (n - 1)

theorem pathEndpoint_adj_lastPred {V : Type u} {G : SimpleGraph V}
    {z : V} {n : ℕ} (hnpos : 0 < n) (P : PathOfLength G z n) :
    G.Adj P.1 (pathLastPred P) := by
  rcases P with ⟨x, p, hp, hplen⟩
  dsimp [pathLastPred]
  have hpred_adj0 :
      G.Adj (p.getVert (p.length - 1)) (p.getVert ((p.length - 1) + 1)) :=
    p.adj_getVert_succ (by omega)
  have hs : (p.length - 1) + 1 = p.length := by omega
  have hn : n - 1 = p.length - 1 := by omega
  rw [hn]
  simpa [hs, SimpleGraph.Walk.getVert_length] using hpred_adj0.symm

theorem path_start_ne_endpoint_of_pos {V : Type u} {G : SimpleGraph V}
    {z x : V} {p : G.Walk z x} (hp : p.IsPath) (hpos : 0 < p.length) :
    z ≠ x := by
  intro hzx
  subst x
  have hnodup : p.support.Nodup := hp.support_nodup
  have h0lt : 0 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hnlt : p.length < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have h0get : p.support[0]? = some z := by
    rw [List.getElem?_eq_getElem h0lt]
    rw [← SimpleGraph.Walk.getVert_eq_support_getElem p (by omega : 0 ≤ p.length)]
    rw [SimpleGraph.Walk.getVert_zero]
  have hnget : p.support[p.length]? = some z := by
    rw [List.getElem?_eq_getElem hnlt]
    rw [← SimpleGraph.Walk.getVert_eq_support_getElem p le_rfl]
    rw [SimpleGraph.Walk.getVert_length]
  have hidx : 0 = p.length :=
    (List.getElem?_inj (i := 0) (j := p.length) h0lt hnodup).mp
      (h0get.trans hnget.symm)
  omega

noncomputable def twoForwardExtension {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (P : PathOfLength G z n) (i : Fin 2) :
    PathOfLength G z (n + 1) :=
  let hpred := pathEndpoint_adj_lastPred hnpos P
  let y := twoForwardVertex G hmin hpred i
  let hxy := twoForwardVertex_adj G hmin hpred i
  let hy_ne_pred := twoForwardVertex_ne_pred G hmin hpred i
  have hpred_eq : pathLastPred P = P.2.1.getVert (P.2.1.length - 1) := by
    dsimp [pathLastPred]
    rw [P.2.2.2]
  ⟨y, ⟨P.2.1.concat hxy,
    concat_isPath_of_girth_ge hg P.2.2.1 hxy
      (by
        rw [P.2.2.2]
        exact hshort)
      (Or.inr (by rwa [← hpred_eq])),
    by
      rw [SimpleGraph.Walk.length_concat, P.2.2.2]⟩⟩

theorem twoForwardExtension_fst {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (P : PathOfLength G z n) (i : Fin 2) :
    (twoForwardExtension G hg hmin hnpos hshort P i).1 =
      twoForwardVertex G hmin (pathEndpoint_adj_lastPred hnpos P) i := by
  rfl

def pathPrefixOfLength {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {z : V} {n : ℕ} (R : PathOfLength G z (n + 1)) :
    PathOfLength G z n :=
  let x := R.2.1.getVert n
  let hxmem : x ∈ R.2.1.support := R.2.1.getVert_mem_support n
  ⟨x, ⟨R.2.1.takeUntil x hxmem, R.2.2.1.takeUntil hxmem,
    by
      rw [SimpleGraph.Walk.length_takeUntil]
      dsimp [x]
      apply idxOf_getVert_of_isPath R.2.2.1
      have hlen : R.2.1.length = n + 1 := R.2.2.2
      omega⟩⟩

theorem getVert_concat_length {V : Type u} {G : SimpleGraph V}
    {z x y : V} (p : G.Walk z x) (hxy : G.Adj x y) :
    (p.concat hxy).getVert p.length = x := by
  have hle : p.length ≤ (p.concat hxy).length := by
    rw [SimpleGraph.Walk.length_concat]
    omega
  have hidx_lt : p.length < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  calc
    (p.concat hxy).getVert p.length =
        (p.concat hxy).support[p.length] := by
          exact SimpleGraph.Walk.getVert_eq_support_getElem (p.concat hxy) hle
    _ = (p.support ++ [y])[p.length] := by
          apply List.getElem_of_eq (SimpleGraph.Walk.support_concat p hxy)
    _ = p.support[p.length] := by
          exact List.getElem_append_left hidx_lt
    _ = p.getVert p.length := by
          exact (SimpleGraph.Walk.getVert_eq_support_getElem p le_rfl).symm
    _ = x := SimpleGraph.Walk.getVert_length p

theorem getVert_concat_of_le_length {V : Type u} {G : SimpleGraph V}
    {z x y : V} (p : G.Walk z x) (hxy : G.Adj x y) {i : ℕ}
    (hi : i ≤ p.length) :
    (p.concat hxy).getVert i = p.getVert i := by
  have hle : i ≤ (p.concat hxy).length := by
    rw [SimpleGraph.Walk.length_concat]
    omega
  have hidx_lt : i < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hconcat_idx_lt : i < (p.concat hxy).support.length := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_concat]
    omega
  have happ_idx_lt : i < (p.support ++ [y]).length := by
    rw [List.length_append]
    simp
    omega
  calc
    (p.concat hxy).getVert i =
        (p.concat hxy).support[i]'hconcat_idx_lt := by
          exact SimpleGraph.Walk.getVert_eq_support_getElem (p.concat hxy) hle
    _ = (p.support ++ [y])[i]'happ_idx_lt := by
          apply List.getElem_of_eq (SimpleGraph.Walk.support_concat p hxy)
    _ = p.support[i]'hidx_lt := by
          exact List.getElem_append_left hidx_lt
    _ = p.getVert i := by
          exact (SimpleGraph.Walk.getVert_eq_support_getElem p hi).symm

theorem isNonreturning_concat {V : Type u} {G : SimpleGraph V}
    {a b c : V} {p : G.Walk a b} (hnr : IsNonreturning p) (hbc : G.Adj b c)
    (hnot_prev : p.length = 0 ∨ c ≠ p.getVert (p.length - 1)) :
    IsNonreturning (p.concat hbc) := by
  intro i hi
  rw [SimpleGraph.Walk.length_concat] at hi
  by_cases hinside : i + 2 ≤ p.length
  · rw [getVert_concat_of_le_length p hbc (by omega)]
    rw [getVert_concat_of_le_length p hbc hinside]
    exact hnr i hinside
  · have hlast : i + 2 = p.length + 1 := by omega
    have ipred : i = p.length - 1 := by omega
    have hile : i ≤ p.length := by omega
    rw [getVert_concat_of_le_length p hbc hile]
    rw [hlast, ← SimpleGraph.Walk.length_concat p hbc, SimpleGraph.Walk.getVert_length]
    rcases hnot_prev with hzero | hne
    · omega
    · rw [ipred]
      exact hne.symm

theorem pathOfLength_endpoint_injective {V : Type u} {G : SimpleGraph V}
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {z : V}
    (hsmall : n + n < g) :
    Function.Injective (fun P : PathOfLength G z n => P.1) := by
  intro P Q hPQ
  rcases P with ⟨x, p, hp, hplen⟩
  rcases Q with ⟨y, q, hq, hqlen⟩
  dsimp at hPQ
  subst y
  have hpaths : (⟨p, hp⟩ : G.Path z x) = ⟨q, hq⟩ := by
    apply path_eq_of_length_sum_lt_egirth hg hp hq
    omega
  have hpq : p = q := congrArg (fun r : G.Path z x => r.1) hpaths
  subst q
  rfl

abbrev NonreturningWalkOfLength {V : Type u} (G : SimpleGraph V) (z : V) (n : ℕ) :=
  Σ x : V, {p : G.Walk z x // IsNonreturning p ∧ p.length = n}

def nonreturningLastPred {V : Type u} {G : SimpleGraph V} {z : V} {n : ℕ}
    (N : NonreturningWalkOfLength G z n) : V :=
  N.2.1.getVert (n - 1)

theorem nonreturningEndpoint_adj_lastPred {V : Type u} {G : SimpleGraph V}
    {z : V} {n : ℕ} (hnpos : 0 < n) (N : NonreturningWalkOfLength G z n) :
    G.Adj N.1 (nonreturningLastPred N) := by
  rcases N with ⟨x, p, hpnr, hplen⟩
  dsimp [nonreturningLastPred]
  have hpred_adj0 :
      G.Adj (p.getVert (p.length - 1)) (p.getVert ((p.length - 1) + 1)) :=
    p.adj_getVert_succ (by omega)
  have hs : (p.length - 1) + 1 = p.length := by omega
  have hn : n - 1 = p.length - 1 := by omega
  rw [hn]
  simpa [hs, SimpleGraph.Walk.getVert_length] using hpred_adj0.symm

def nonreturningToPathOfLength {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {z : V} (hshort : n < g) (N : NonreturningWalkOfLength G z n) :
    PathOfLength G z n :=
  ⟨N.1, ⟨N.2.1,
    isPath_of_isNonreturning_of_length_lt_girth hg N.2.1 N.2.2.1 (by
      rw [N.2.2.2]
      exact hshort),
    N.2.2.2⟩⟩

theorem nonreturning_endpoint_injective {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {z : V} (hsmall : n + n < g) :
    Function.Injective (fun N : NonreturningWalkOfLength G z n => N.1) := by
  intro A B hAB
  have hpath :
      nonreturningToPathOfLength hg (z := z) (n := n) (by omega) A =
        nonreturningToPathOfLength hg (z := z) (n := n) (by omega) B :=
    pathOfLength_endpoint_injective hg hsmall hAB
  rcases A with ⟨x, p, hpnr, hplen⟩
  rcases B with ⟨y, q, hqnr, hqlen⟩
  dsimp [nonreturningToPathOfLength] at hpath
  cases hpath
  rfl

theorem finite_nonreturningWalkOfLength {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {z : V} (hsmall : n + n < g) :
    Finite (NonreturningWalkOfLength G z n) :=
  Finite.of_injective
    (fun N : NonreturningWalkOfLength G z n => N.1)
    (nonreturning_endpoint_injective hg hsmall)

abbrev NonreturningExtensionChoice {V : Type u} {G : SimpleGraph V}
    {z : V} {n : ℕ} (N : NonreturningWalkOfLength G z n) :=
  {y : V // G.Adj N.1 y ∧ (n = 0 ∨ y ≠ N.2.1.getVert (n - 1))}

def nonreturningExtension {V : Type u} {G : SimpleGraph V}
    {z : V} {n : ℕ} (N : NonreturningWalkOfLength G z n)
    (Y : NonreturningExtensionChoice N) :
    NonreturningWalkOfLength G z (n + 1) :=
  ⟨Y.1, ⟨N.2.1.concat Y.2.1,
    isNonreturning_concat N.2.2.1 Y.2.1 (by
      rcases Y.2.2 with hn0 | hne
      · left
        rw [N.2.2.2, hn0]
      · right
        rwa [N.2.2.2]),
    by
      rw [SimpleGraph.Walk.length_concat, N.2.2.2]⟩⟩

theorem degree_sub_one_le_nonreturningExtensionChoice_card {V : Type u}
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {z : V} {n : ℕ} (hnpos : 0 < n) (N : NonreturningWalkOfLength G z n) :
    G.degree N.1 - 1 ≤ Nat.card (NonreturningExtensionChoice N) := by
  classical
  let pred := nonreturningLastPred N
  have hpred_adj : G.Adj N.1 pred := by
    simpa [pred] using nonreturningEndpoint_adj_lastPred hnpos N
  have hpred_mem : pred ∈ G.neighborFinset N.1 := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hpred_adj
  let f : ((G.neighborFinset N.1).erase pred) → NonreturningExtensionChoice N := fun y =>
    ⟨y.1,
      by
        have hyneigh : y.1 ∈ G.neighborFinset N.1 :=
          (Finset.mem_erase.mp y.2).2
        rwa [SimpleGraph.mem_neighborFinset] at hyneigh,
      by
        right
        have hyne : y.1 ≠ pred := (Finset.mem_erase.mp y.2).1
        simpa [pred, nonreturningLastPred] using hyne⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun Y : NonreturningExtensionChoice N => Y.1) hab
  have hcard := Nat.card_le_card_of_injective f hf
  have hdomain_card :
      Nat.card ((G.neighborFinset N.1).erase pred) = G.degree N.1 - 1 := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_coe ((G.neighborFinset N.1).erase pred)]
    rw [Finset.card_erase_of_mem hpred_mem]
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  rw [← hdomain_card]
  exact hcard

theorem nonreturningExtension_injective {V : Type u} {G : SimpleGraph V}
    {z : V} {n : ℕ} :
    Function.Injective
      (fun A : Σ N : NonreturningWalkOfLength G z n, NonreturningExtensionChoice N =>
        nonreturningExtension A.1 A.2) := by
  intro A B h
  rcases A with ⟨N, Y⟩
  rcases B with ⟨M, Z⟩
  rcases N with ⟨x, p, hpnr, hplen⟩
  rcases M with ⟨x', q, hqnr, hqlen⟩
  rcases Y with ⟨y, hy_adj, hy_not⟩
  rcases Z with ⟨y', hz_adj, hz_not⟩
  dsimp [nonreturningExtension] at h
  injection h with hy hsub
  subst y'
  have hwalk : p.concat hy_adj = q.concat hz_adj := by
    exact congrArg Subtype.val (eq_of_heq hsub)
  obtain ⟨hx, hpq⟩ := SimpleGraph.Walk.concat_inj hwalk
  cases hx
  have hpq' : p = q := by simpa using hpq
  cases hpq'
  rfl

abbrev NonreturningWalksOfLength {V : Type u} (G : SimpleGraph V) (n : ℕ) :=
  Σ z : V, NonreturningWalkOfLength G z n

def nonreturningWalksLengthZeroEquivVertices {V : Type u} (G : SimpleGraph V) :
    NonreturningWalksOfLength G 0 ≃ V where
  toFun W := W.1
  invFun z :=
    ⟨z, z, ⟨SimpleGraph.Walk.nil,
      by
        constructor
        · intro i hi
          simp at hi
        · simp⟩⟩
  left_inv W := by
    rcases W with ⟨z, x, p, hnr, hplen⟩
    cases p with
    | nil =>
        rfl
    | cons h q =>
        simp at hplen
  right_inv z := rfl

theorem nonreturningWalks_length_zero_natCard_eq_vertices {V : Type u}
    (G : SimpleGraph V) [Fintype V] :
    Nat.card (NonreturningWalksOfLength G 0) = Fintype.card V := by
  calc
    Nat.card (NonreturningWalksOfLength G 0) = Nat.card V :=
      Nat.card_congr (nonreturningWalksLengthZeroEquivVertices G)
    _ = Fintype.card V := Nat.card_eq_fintype_card

theorem finite_nonreturningWalksOfLength {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (hsmall : n + n < g) :
    Finite (NonreturningWalksOfLength G n) := by
  exact @Finite.instSigma V
    (fun z => NonreturningWalkOfLength G z n)
    inferInstance
    (fun z => finite_nonreturningWalkOfLength (G := G) (z := z) hg hsmall)

abbrev NonreturningWalkExtensionsOfLength {V : Type u} (G : SimpleGraph V) (n : ℕ) :=
  Σ W : NonreturningWalksOfLength G n, NonreturningExtensionChoice W.2

def nonreturningWalkExtension {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (A : NonreturningWalkExtensionsOfLength G n) :
    NonreturningWalksOfLength G (n + 1) :=
  ⟨A.1.1, nonreturningExtension A.1.2 A.2⟩

theorem nonreturningWalkExtension_injective {V : Type u} {G : SimpleGraph V}
    {n : ℕ} :
    Function.Injective
      (nonreturningWalkExtension (G := G) (n := n)) := by
  intro A B h
  rcases A with ⟨⟨z, N⟩, Y⟩
  rcases B with ⟨⟨w, M⟩, Z⟩
  dsimp [nonreturningWalkExtension] at h
  injection h with hzw hroot
  subst w
  have hroot' :
      nonreturningExtension N Y = nonreturningExtension M Z :=
    eq_of_heq hroot
  have hpair :
      (⟨N, Y⟩ : Σ N : NonreturningWalkOfLength G z n, NonreturningExtensionChoice N) =
        ⟨M, Z⟩ :=
    nonreturningExtension_injective hroot'
  cases hpair
  rfl

theorem nonreturningWalkExtensions_card_le_succ {V : Type u} {G : SimpleGraph V}
    {n : ℕ} [Finite (NonreturningWalksOfLength G (n + 1))] :
    Nat.card (NonreturningWalkExtensionsOfLength G n) ≤
      Nat.card (NonreturningWalksOfLength G (n + 1)) := by
  exact Nat.card_le_card_of_injective
    (nonreturningWalkExtension (G := G) (n := n))
    nonreturningWalkExtension_injective

theorem nonreturningWalkExtensions_natCard_eq_sum_choices {V : Type u}
    {G : SimpleGraph V} {n : ℕ} [Finite V] [Fintype (NonreturningWalksOfLength G n)] :
    Nat.card (NonreturningWalkExtensionsOfLength G n) =
      ∑ W : NonreturningWalksOfLength G n, Nat.card (NonreturningExtensionChoice W.2) := by
  exact Nat.card_sigma

theorem sum_degree_sub_one_le_nonreturningWalks_succ_card {V : Type u}
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} [Fintype (NonreturningWalksOfLength G n)]
    [Finite (NonreturningWalksOfLength G (n + 1))] (hnpos : 0 < n) :
    (∑ W : NonreturningWalksOfLength G n, (G.degree W.2.1 - 1)) ≤
      Nat.card (NonreturningWalksOfLength G (n + 1)) := by
  have hsum_le :
      (∑ W : NonreturningWalksOfLength G n, (G.degree W.2.1 - 1)) ≤
        ∑ W : NonreturningWalksOfLength G n, Nat.card (NonreturningExtensionChoice W.2) := by
    simpa using
      (Finset.sum_le_sum (s := Finset.univ)
        (fun (W : NonreturningWalksOfLength G n) hW =>
          degree_sub_one_le_nonreturningExtensionChoice_card hnpos W.2))
  have hdomain :
      Nat.card (NonreturningWalkExtensionsOfLength G n) =
        ∑ W : NonreturningWalksOfLength G n, Nat.card (NonreturningExtensionChoice W.2) :=
    nonreturningWalkExtensions_natCard_eq_sum_choices
  have hnext :
      Nat.card (NonreturningWalkExtensionsOfLength G n) ≤
        Nat.card (NonreturningWalksOfLength G (n + 1)) :=
    nonreturningWalkExtensions_card_le_succ
  have hchoices_le :
      (∑ W : NonreturningWalksOfLength G n, Nat.card (NonreturningExtensionChoice W.2)) ≤
        Nat.card (NonreturningWalksOfLength G (n + 1)) := by
    rw [← hdomain]
    exact hnext
  exact hsum_le.trans hchoices_le

abbrev NonreturningWalksAtMost {V : Type u} (G : SimpleGraph V) (r : ℕ) :=
  Σ n : {n : ℕ // n ≤ r}, NonreturningWalksOfLength G n.1

def nonreturningWalksAtMostEndpoints {V : Type u} {G : SimpleGraph V} {r : ℕ}
    (W : NonreturningWalksAtMost G r) : V × V :=
  (W.2.1, W.2.2.1)

theorem nonreturningWalksAtMost_endpoints_injective {V : Type u}
    {G : SimpleGraph V} [DecidableEq V] {g r : ℕ}
    (hg : (g : ℕ∞) ≤ G.egirth) (hsmall : r + r < g) :
    Function.Injective (nonreturningWalksAtMostEndpoints (G := G) (r := r)) := by
  intro A B hAB
  rcases A with ⟨⟨n, hn⟩, z, x, p, hpnr, hplen⟩
  rcases B with ⟨⟨m, hm⟩, w, y, q, hqnr, hqlen⟩
  dsimp [nonreturningWalksAtMostEndpoints] at hAB
  injection hAB with hzw hxy
  subst w
  subst y
  have hplen_nat : p.length = n := by simpa using hplen
  have hqlen_nat : q.length = m := by simpa using hqlen
  have hp : p.IsPath := by
    apply isPath_of_isNonreturning_of_length_lt_girth hg p hpnr
    rw [hplen_nat]
    omega
  have hq : q.IsPath := by
    apply isPath_of_isNonreturning_of_length_lt_girth hg q hqnr
    rw [hqlen_nat]
    omega
  have hpaths : (⟨p, hp⟩ : G.Path z x) = ⟨q, hq⟩ := by
    apply path_eq_of_length_sum_lt_egirth hg hp hq
    rw [hplen_nat, hqlen_nat]
    omega
  have hpq : p = q := congrArg (fun R : G.Path z x => R.1) hpaths
  subst q
  have hn_eq : n = p.length := hplen_nat.symm
  have hm_eq : m = p.length := hqlen_nat.symm
  subst n
  subst m
  rfl

theorem nonreturningWalksAtMost_card_le_vertex_pairs {V : Type u}
    {G : SimpleGraph V} [Finite V] [DecidableEq V] {g r : ℕ}
    (hg : (g : ℕ∞) ≤ G.egirth) (hsmall : r + r < g) :
    Nat.card (NonreturningWalksAtMost G r) ≤ Nat.card (V × V) :=
  Nat.card_le_card_of_injective
    (nonreturningWalksAtMostEndpoints (G := G) (r := r))
    (nonreturningWalksAtMost_endpoints_injective hg hsmall)

theorem nonreturningWalksAtMost_card_le_card_sq {V : Type u}
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] {g r : ℕ}
    (hg : (g : ℕ∞) ≤ G.egirth) (hsmall : r + r < g) :
    Nat.card (NonreturningWalksAtMost G r) ≤ Fintype.card V * Fintype.card V := by
  have h := nonreturningWalksAtMost_card_le_vertex_pairs (G := G) hg hsmall
  simpa [Nat.card_prod, Nat.card_eq_fintype_card] using h

def nonreturningWalksLengthOneEquivDart {V : Type u} (G : SimpleGraph V) :
    NonreturningWalksOfLength G 1 ≃ G.Dart where
  toFun N :=
    ⟨(N.1, N.2.1), by
      exact N.2.2.1.adj_of_length_eq_one N.2.2.2.2⟩
  invFun d :=
    ⟨d.fst, d.snd,
      ⟨SimpleGraph.Walk.cons d.adj SimpleGraph.Walk.nil,
        by
          constructor
          · intro i hi
            simp at hi
          · simp⟩⟩
  left_inv N := by
    rcases N with ⟨z, x, p, hnr, hplen⟩
    cases p with
    | nil =>
        simp at hplen
    | cons h q =>
        cases q with
        | nil =>
            rfl
        | cons h' q =>
            simp at hplen
  right_inv d := by
    ext <;> rfl

theorem nonreturningWalks_length_one_natCard_eq_sum_degrees {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    Nat.card (NonreturningWalksOfLength G 1) = ∑ v, G.degree v := by
  calc
    Nat.card (NonreturningWalksOfLength G 1) = Nat.card G.Dart :=
      Nat.card_congr (nonreturningWalksLengthOneEquivDart G)
    _ = Fintype.card G.Dart := Nat.card_eq_fintype_card
    _ = ∑ v, G.degree v := SimpleGraph.dart_card_eq_sum_degrees G

abbrev PathOfLengthAtMost {V : Type u} (G : SimpleGraph V) (z : V) (r : ℕ) :=
  Σ n : {n : ℕ // n ≤ r}, PathOfLength G z n

def pathAtMostEndpoint {V : Type u} {G : SimpleGraph V} {z : V} {r : ℕ}
    (P : PathOfLengthAtMost G z r) : V :=
  P.2.1

theorem pathAtMost_endpoint_injective {V : Type u} {G : SimpleGraph V}
    {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {z : V}
    (hsmall : r + r < g) :
    Function.Injective (pathAtMostEndpoint (G := G) (z := z) (r := r)) := by
  intro P Q hPQ
  rcases P with ⟨⟨n, hn⟩, x, p, hp, hplen⟩
  rcases Q with ⟨⟨m, hm⟩, y, q, hq, hqlen⟩
  dsimp [pathAtMostEndpoint] at hPQ
  subst y
  have hplen_nat : p.length = n := by simpa using hplen
  have hqlen_nat : q.length = m := by simpa using hqlen
  have hpaths : (⟨p, hp⟩ : G.Path z x) = ⟨q, hq⟩ := by
    apply path_eq_of_length_sum_lt_egirth hg hp hq
    rw [hplen_nat, hqlen_nat]
    omega
  have hpq : p = q := congrArg (fun r : G.Path z x => r.1) hpaths
  subst q
  have hnm : n = m := by
    omega
  subst n
  subst m
  rfl

theorem pathAtMost_card_le_vertices {V : Type u} {G : SimpleGraph V} [Finite V]
    {z : V} {r : ℕ}
    (hinj : Function.Injective (pathAtMostEndpoint (G := G) (z := z) (r := r))) :
    Nat.card (PathOfLengthAtMost G z r) ≤ Nat.card V :=
  Nat.card_le_card_of_injective pathAtMostEndpoint hinj

theorem pathPrefix_twoForwardExtension {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g) (hsmall : n + n < g)
    (P : PathOfLength G z n) (i : Fin 2) :
    pathPrefixOfLength (twoForwardExtension G hg hmin hnpos hshort P i) = P := by
  rcases P with ⟨x, p, hp, hplen⟩
  subst n
  apply pathOfLength_endpoint_injective hg hsmall
  simp [twoForwardExtension, pathPrefixOfLength]
  exact getVert_concat_length p _

theorem twoForwardExtension_injective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g) (hsmall : n + n < g) :
    Function.Injective
      (fun Q : PathOfLength G z n × Fin 2 =>
        twoForwardExtension G hg hmin hnpos hshort Q.1 Q.2) := by
  intro A B h
  rcases A with ⟨P, i⟩
  rcases B with ⟨Q, j⟩
  have hP : P = Q := by
    have hpref := congrArg pathPrefixOfLength h
    rw [pathPrefix_twoForwardExtension G hg hmin hnpos hshort hsmall P i] at hpref
    rw [pathPrefix_twoForwardExtension G hg hmin hnpos hshort hsmall Q j] at hpref
    exact hpref
  cases hP
  have hend : (twoForwardExtension G hg hmin hnpos hshort P i).1 =
      (twoForwardExtension G hg hmin hnpos hshort P j).1 := by
    exact congrArg (fun R : PathOfLength G z (n + 1) => R.1) h
  rw [twoForwardExtension_fst G hg hmin hnpos hshort P i] at hend
  rw [twoForwardExtension_fst G hg hmin hnpos hshort P j] at hend
  have hi : i = j :=
    twoForwardVertex_injective G hmin (pathEndpoint_adj_lastPred hnpos P) hend
  cases hi
  rfl

noncomputable def dForwardExtension {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (P : PathOfLength G z n) (i : Fin (d - 1)) :
    PathOfLength G z (n + 1) :=
  let hpred := pathEndpoint_adj_lastPred hnpos P
  let y := dForwardVertex G hmin hpred i
  let hxy := dForwardVertex_adj G hmin hpred i
  let hy_ne_pred := dForwardVertex_ne_pred G hmin hpred i
  have hpred_eq : pathLastPred P = P.2.1.getVert (P.2.1.length - 1) := by
    dsimp [pathLastPred]
    rw [P.2.2.2]
  ⟨y, ⟨P.2.1.concat hxy,
    concat_isPath_of_girth_ge hg P.2.2.1 hxy
      (by
        rw [P.2.2.2]
        exact hshort)
      (Or.inr (by rwa [← hpred_eq])),
    by
      rw [SimpleGraph.Walk.length_concat, P.2.2.2]⟩⟩

theorem dForwardExtension_fst {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (P : PathOfLength G z n) (i : Fin (d - 1)) :
    (dForwardExtension G hg hmin hnpos hshort P i).1 =
      dForwardVertex G hmin (pathEndpoint_adj_lastPred hnpos P) i := by
  rfl

theorem pathPrefix_dForwardExtension {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g) (hsmall : n + n < g)
    (P : PathOfLength G z n) (i : Fin (d - 1)) :
    pathPrefixOfLength (dForwardExtension G hg hmin hnpos hshort P i) = P := by
  rcases P with ⟨x, p, hp, hplen⟩
  subst n
  apply pathOfLength_endpoint_injective hg hsmall
  simp [dForwardExtension, pathPrefixOfLength]
  exact getVert_concat_length p _

theorem dForwardExtension_injective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g) (hsmall : n + n < g) :
    Function.Injective
      (fun Q : PathOfLength G z n × Fin (d - 1) =>
        dForwardExtension G hg hmin hnpos hshort Q.1 Q.2) := by
  intro A B h
  rcases A with ⟨P, i⟩
  rcases B with ⟨Q, j⟩
  have hP : P = Q := by
    have hpref := congrArg pathPrefixOfLength h
    rw [pathPrefix_dForwardExtension G hg hmin hnpos hshort hsmall P i] at hpref
    rw [pathPrefix_dForwardExtension G hg hmin hnpos hshort hsmall Q j] at hpref
    exact hpref
  cases hP
  have hend : (dForwardExtension G hg hmin hnpos hshort P i).1 =
      (dForwardExtension G hg hmin hnpos hshort P j).1 := by
    exact congrArg (fun R : PathOfLength G z (n + 1) => R.1) h
  rw [dForwardExtension_fst G hg hmin hnpos hshort P i] at hend
  rw [dForwardExtension_fst G hg hmin hnpos hshort P j] at hend
  have hi : i = j :=
    dForwardVertex_injective G hmin (pathEndpoint_adj_lastPred hnpos P) hend
  cases hi
  rfl

abbrev AvoidingPathOfLength {V : Type u} (G : SimpleGraph V)
    (z forbidden : V) (n : ℕ) :=
  Σ x : V, {p : G.Walk z x // p.IsPath ∧ p.length = n ∧
    (0 < n → p.getVert 1 ≠ forbidden)}

def avoidingToPathOfLength {V : Type u} {G : SimpleGraph V}
    {z forbidden : V} {n : ℕ}
    (A : AvoidingPathOfLength G z forbidden n) :
    PathOfLength G z n :=
  ⟨A.1, ⟨A.2.1, A.2.2.1, A.2.2.2.1⟩⟩

theorem avoiding_endpoint_injective {V : Type u} {G : SimpleGraph V}
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {z forbidden : V}
    (hsmall : n + n < g) :
    Function.Injective (fun A : AvoidingPathOfLength G z forbidden n => A.1) := by
  intro A B hAB
  have hpath :
      avoidingToPathOfLength A = avoidingToPathOfLength B :=
    pathOfLength_endpoint_injective hg hsmall hAB
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  rcases B with ⟨y, q, hq, hqlen, havoidq⟩
  dsimp [avoidingToPathOfLength] at hpath
  cases hpath
  rfl

theorem finite_avoidingPathOfLength {V : Type u} {G : SimpleGraph V}
    [Finite V] {z forbidden : V} {n : ℕ}
    (hinj : Function.Injective
      (fun A : AvoidingPathOfLength G z forbidden n => A.1)) :
    Finite (AvoidingPathOfLength G z forbidden n) :=
  Finite.of_injective (fun A : AvoidingPathOfLength G z forbidden n => A.1) hinj

abbrev AvoidingPathOfLengthAtMost {V : Type u} (G : SimpleGraph V)
    (z forbidden : V) (r : ℕ) :=
  Σ n : {n : ℕ // n ≤ r}, AvoidingPathOfLength G z forbidden n

def avoidingAtMostEndpoint {V : Type u} {G : SimpleGraph V} {z forbidden : V} {r : ℕ}
    (A : AvoidingPathOfLengthAtMost G z forbidden r) : V :=
  A.2.1

theorem avoidingAtMost_endpoint_injective {V : Type u} {G : SimpleGraph V}
    {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) {z forbidden : V}
    (hsmall : r + r < g) :
    Function.Injective
      (avoidingAtMostEndpoint (G := G) (z := z) (forbidden := forbidden) (r := r)) := by
  intro A B hAB
  rcases A with ⟨⟨n, hn⟩, x, p, hp, hplen, havoid⟩
  rcases B with ⟨⟨m, hm⟩, y, q, hq, hqlen, havoidq⟩
  dsimp [avoidingAtMostEndpoint] at hAB
  subst y
  have hplen_nat : p.length = n := by simpa using hplen
  have hqlen_nat : q.length = m := by simpa using hqlen
  have hpaths : (⟨p, hp⟩ : G.Path z x) = ⟨q, hq⟩ := by
    apply path_eq_of_length_sum_lt_egirth hg hp hq
    rw [hplen_nat, hqlen_nat]
    omega
  have hpq : p = q := congrArg (fun r : G.Path z x => r.1) hpaths
  subst q
  have hnm : n = m := by
    omega
  subst n
  subst m
  rfl

theorem twoForwardExtension_walk {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (P : PathOfLength G z n) (i : Fin 2) :
    (twoForwardExtension G hg hmin hnpos hshort P i).2.1 =
      P.2.1.concat
        (twoForwardVertex_adj G hmin (pathEndpoint_adj_lastPred hnpos P) i) := by
  rfl

noncomputable def avoidingForwardExtension {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z forbidden : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (A : AvoidingPathOfLength G z forbidden n) (i : Fin 2) :
    AvoidingPathOfLength G z forbidden (n + 1) := by
  let P := avoidingToPathOfLength A
  let R := twoForwardExtension G hg hmin hnpos hshort P i
  refine ⟨R.1, ⟨R.2.1, R.2.2.1, R.2.2.2, ?_⟩⟩
  intro _
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  dsimp [P, R, avoidingToPathOfLength]
  have hle_one : 1 ≤ p.length := by omega
  rw [twoForwardExtension_walk]
  change (p.concat _).getVert 1 ≠ forbidden
  rw [getVert_concat_of_le_length p _ hle_one]
  exact havoid hnpos

theorem avoidingToPathOfLength_injective {V : Type u} {G : SimpleGraph V}
    {z forbidden : V} {n : ℕ} :
    Function.Injective
      (avoidingToPathOfLength :
        AvoidingPathOfLength G z forbidden n → PathOfLength G z n) := by
  intro A B h
  rcases A with ⟨x, p, hp, hplen, havoid⟩
  rcases B with ⟨y, q, hq, hqlen, havoidq⟩
  dsimp [avoidingToPathOfLength] at h
  cases h
  rfl

theorem avoidingForwardExtension_toPath {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z forbidden : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (A : AvoidingPathOfLength G z forbidden n) (i : Fin 2) :
    avoidingToPathOfLength (avoidingForwardExtension G hg hmin hnpos hshort A i) =
      twoForwardExtension G hg hmin hnpos hshort (avoidingToPathOfLength A) i := by
  rfl

theorem avoidingForwardExtension_injective {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z forbidden : V} (hnpos : 0 < n) (hshort : n + 1 < g) (hsmall : n + n < g) :
    Function.Injective
      (fun Q : AvoidingPathOfLength G z forbidden n × Fin 2 =>
        avoidingForwardExtension G hg hmin hnpos hshort Q.1 Q.2) := by
  intro A B h
  rcases A with ⟨A, i⟩
  rcases B with ⟨B, j⟩
  have hpath := congrArg avoidingToPathOfLength h
  rw [avoidingForwardExtension_toPath G hg hmin hnpos hshort A i] at hpath
  rw [avoidingForwardExtension_toPath G hg hmin hnpos hshort B j] at hpath
  have hpair :
      (avoidingToPathOfLength A, i) = (avoidingToPathOfLength B, j) :=
    twoForwardExtension_injective G hg hmin hnpos hshort hsmall hpath
  injection hpair with hA hi
  have hAB : A = B := avoidingToPathOfLength_injective hA
  cases hAB
  cases hi
  rfl

theorem two_le_avoidingPathOfLength_one_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z forbidden : V} (hpred : G.Adj z forbidden) (hsmall : 1 + 1 < g) :
    2 ≤ Nat.card (AvoidingPathOfLength G z forbidden 1) := by
  have hinj_endpoint :=
    avoiding_endpoint_injective hg (z := z) (forbidden := forbidden) hsmall
  have hfinite : Finite (AvoidingPathOfLength G z forbidden 1) :=
    finite_avoidingPathOfLength hinj_endpoint
  letI := hfinite
  let f : Fin 2 → AvoidingPathOfLength G z forbidden 1 := fun i =>
    let y := twoForwardVertex G hmin hpred i
    let hzy := twoForwardVertex_adj G hmin hpred i
    ⟨y, ⟨SimpleGraph.Walk.cons hzy SimpleGraph.Walk.nil,
      by
        constructor
        · rw [SimpleGraph.Walk.isPath_def]
          simp [SimpleGraph.Walk.support_cons, hzy.ne]
        constructor
        · simp
        · intro _
          have hlen :
              (SimpleGraph.Walk.cons hzy SimpleGraph.Walk.nil).length = 1 := by
            simp
          rw [← hlen, SimpleGraph.Walk.getVert_length]
          exact twoForwardVertex_ne_pred G hmin hpred i⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply twoForwardVertex_injective G hmin hpred
    exact congrArg (fun A : AvoidingPathOfLength G z forbidden 1 => A.1) hij
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_fin] using hcard

theorem two_mul_avoidingPath_card_le_succ {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z forbidden : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (hsmall : n + n < g) (hnextsmall : (n + 1) + (n + 1) < g) :
    2 * Nat.card (AvoidingPathOfLength G z forbidden n) ≤
      Nat.card (AvoidingPathOfLength G z forbidden (n + 1)) := by
  have hinj :=
    avoidingForwardExtension_injective G hg hmin hnpos hshort hsmall
      (z := z) (forbidden := forbidden)
  have htarget_finite : Finite (AvoidingPathOfLength G z forbidden (n + 1)) :=
    finite_avoidingPathOfLength
      (avoiding_endpoint_injective hg hnextsmall)
  letI := htarget_finite
  have hcard := Nat.card_le_card_of_injective
    (fun Q : AvoidingPathOfLength G z forbidden n × Fin 2 =>
      avoidingForwardExtension G hg hmin hnpos hshort Q.1 Q.2)
    hinj
  simpa [Nat.card_prod, Nat.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hcard

theorem two_pow_le_avoidingPath_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z forbidden : V} (hpred : G.Adj z forbidden)
    (hnpos : 0 < n) (hsmall : n + n < g) :
    2 ^ n ≤ Nat.card (AvoidingPathOfLength G z forbidden n) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          exact two_le_avoidingPathOfLength_one_card G hg hmin hpred hsmall
      | succ m =>
          have hmpos : 0 < m + 1 := by omega
          have hsmall_m : (m + 1) + (m + 1) < g := by omega
          have ih_m : 2 ^ (m + 1) ≤
              Nat.card (AvoidingPathOfLength G z forbidden (m + 1)) :=
            ih (by omega) hsmall_m
          have hshort : (m + 1) + 1 < g := by omega
          have hrec :
              2 * Nat.card (AvoidingPathOfLength G z forbidden (m + 1)) ≤
                Nat.card (AvoidingPathOfLength G z forbidden ((m + 1) + 1)) :=
            two_mul_avoidingPath_card_le_succ G hg hmin hmpos hshort hsmall_m hsmall
          rw [pow_succ]
          rw [Nat.mul_comm (2 ^ (m + 1)) 2]
          exact (Nat.mul_le_mul_left 2 ih_m).trans hrec

theorem forbidden_not_mem_avoiding_support {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {y x v : V} (hxy : G.Adj y x)
    {q : G.Walk y v} (hq : q.IsPath) (hqlen : q.length = n)
    (havoid : 0 < n → q.getVert 1 ≠ x) (hshort : n + 1 < g) :
    x ∉ q.support := by
  have hrev_path : q.reverse.IsPath := hq.reverse
  have hrev_short : q.reverse.length + 1 < g := by
    rw [SimpleGraph.Walk.length_reverse, hqlen]
    exact hshort
  have hnot_prev :
      q.reverse.length = 0 ∨ x ≠ q.reverse.getVert (q.reverse.length - 1) := by
    by_cases hn0 : n = 0
    · left
      rw [SimpleGraph.Walk.length_reverse, hqlen, hn0]
    · right
      have hnpos : 0 < n := by omega
      have hidx : q.length - (q.length - 1) = 1 := by omega
      rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.getVert_reverse]
      rw [hidx]
      exact (havoid hnpos).symm
  have hx_not_rev :
      x ∉ q.reverse.support :=
    support_not_mem_of_short_concat hg hrev_path hxy hrev_short hnot_prev
  intro hx
  apply hx_not_rev
  rw [SimpleGraph.Walk.support_reverse]
  exact List.mem_reverse.mpr hx

theorem cons_avoiding_isPath {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y v : V} (hxy : G.Adj x y)
    {q : G.Walk y v} (hq : q.IsPath) (hqlen : q.length = n)
    (havoid : 0 < n → q.getVert 1 ≠ x) (hshort : n + 1 < g) :
    (SimpleGraph.Walk.cons hxy q).IsPath := by
  have hx_not_q : x ∉ q.support :=
    forbidden_not_mem_avoiding_support hg hxy.symm hq hqlen havoid hshort
  rw [SimpleGraph.Walk.isPath_def]
  rw [SimpleGraph.Walk.support_cons]
  exact hq.support_nodup.cons hx_not_q

theorem edgeRoot_cross_endpoints_ne {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hcross : n + (n + 1) < g)
    (A : AvoidingPathOfLength G x y n) (B : AvoidingPathOfLength G y x n) :
    A.1 ≠ B.1 := by
  intro hend
  rcases A with ⟨a, p, hp, hplen, havoidp⟩
  rcases B with ⟨b, q, hq, hqlen, havoidq⟩
  dsimp at hend
  subst b
  let r : G.Walk x a := SimpleGraph.Walk.cons hxy q
  have hr_path : r.IsPath :=
    cons_avoiding_isPath hg hxy hq hqlen havoidq (by omega)
  have hr_len : r.length = n + 1 := by
    dsimp [r]
    rw [hqlen]
  have hcycle :
      g ≤ r.length + p.length :=
    egirth_bound_of_two_paths_length_lt hg hr_path hp (by
      rw [hr_len, hplen]
      omega)
  rw [hr_len, hplen] at hcycle
  omega

theorem edgeRoot_cross_endpoints_ne_lengths {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n m : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hcross : n + (m + 1) < g)
    (A : AvoidingPathOfLength G x y n) (B : AvoidingPathOfLength G y x m) :
    A.1 ≠ B.1 := by
  intro hend
  rcases A with ⟨a, p, hp, hplen, havoidp⟩
  rcases B with ⟨b, q, hq, hqlen, havoidq⟩
  dsimp at hend
  subst b
  let r : G.Walk x a := SimpleGraph.Walk.cons hxy q
  have hr_path : r.IsPath :=
    cons_avoiding_isPath hg hxy hq hqlen havoidq (by omega)
  have hr_len : r.length = m + 1 := by
    dsimp [r]
    rw [hqlen]
  have hpaths_ne : (⟨r, hr_path⟩ : G.Path x a) ≠ ⟨p, hp⟩ := by
    intro hEq
    have hWalkEq := congrArg (fun R : G.Path x a => R.1) hEq
    by_cases hlen : r.length = p.length
    · have hnpos : 0 < n := by
        rw [hr_len, hplen] at hlen
        omega
      have hfirst := congrArg (fun w : G.Walk x a => w.getVert 1) hWalkEq
      dsimp [r] at hfirst
      rw [SimpleGraph.Walk.getVert_zero] at hfirst
      exact havoidp hnpos hfirst.symm
    · exact hlen (congrArg (fun w : G.Walk x a => w.length) hWalkEq)
  have hcycle :
      g ≤ r.length + p.length :=
    egirth_bound_of_two_distinct_paths hg hr_path hp hpaths_ne
  rw [hr_len, hplen] at hcycle
  omega

def edgeRootEndpoint {V : Type u} {G : SimpleGraph V} {x y : V} {n : ℕ} :
    AvoidingPathOfLength G x y n ⊕ AvoidingPathOfLength G y x n → V
  | Sum.inl A => A.1
  | Sum.inr B => B.1

def edgeRootAtMostEndpoint {V : Type u} {G : SimpleGraph V} {x y : V} {r : ℕ} :
    AvoidingPathOfLengthAtMost G x y r ⊕ AvoidingPathOfLengthAtMost G y x r → V
  | Sum.inl A => A.2.1
  | Sum.inr B => B.2.1

theorem edgeRootEndpoint_injective {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hsmall : n + n < g)
    (hcross : n + (n + 1) < g) :
    Function.Injective (edgeRootEndpoint (G := G) (x := x) (y := y) (n := n)) := by
  intro A B h
  cases A with
  | inl A =>
      cases B with
      | inl B =>
          have hAB :
              A = B :=
            avoiding_endpoint_injective hg (z := x) (forbidden := y) hsmall h
          cases hAB
          rfl
      | inr B =>
          exact False.elim (edgeRoot_cross_endpoints_ne hg hxy hcross A B h)
  | inr A =>
      cases B with
      | inl B =>
          exact False.elim (edgeRoot_cross_endpoints_ne hg hxy hcross B A h.symm)
      | inr B =>
          have hAB :
              A = B :=
            avoiding_endpoint_injective hg (z := y) (forbidden := x) hsmall h
          cases hAB
          rfl

theorem edgeRootAtMostEndpoint_injective {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hsmall : r + r < g)
    (hcross : r + (r + 1) < g) :
    Function.Injective (edgeRootAtMostEndpoint (G := G) (x := x) (y := y) (r := r)) := by
  intro A B h
  cases A with
  | inl A =>
      cases B with
      | inl B =>
          have hAB :
              A = B :=
            avoidingAtMost_endpoint_injective hg (z := x) (forbidden := y) hsmall h
          cases hAB
          rfl
      | inr B =>
          have hcrossAB : A.1.1 + (B.1.1 + 1) < g := by
            exact Nat.lt_of_le_of_lt (by
              exact Nat.add_le_add A.1.2 (Nat.succ_le_succ B.1.2)) hcross
          exact False.elim
            (edgeRoot_cross_endpoints_ne_lengths hg hxy hcrossAB A.2 B.2 h)
  | inr A =>
      cases B with
      | inl B =>
          have hcrossBA : B.1.1 + (A.1.1 + 1) < g := by
            exact Nat.lt_of_le_of_lt (by
              exact Nat.add_le_add B.1.2 (Nat.succ_le_succ A.1.2)) hcross
          exact False.elim
            (edgeRoot_cross_endpoints_ne_lengths hg hxy hcrossBA B.2 A.2 h.symm)
      | inr B =>
          have hAB :
              A = B :=
            avoidingAtMost_endpoint_injective hg (z := y) (forbidden := x) hsmall h
          cases hAB
          rfl

theorem edgeRootAtMost_card_le_vertices {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hsmall : r + r < g)
    (hcross : r + (r + 1) < g) :
    Nat.card (AvoidingPathOfLengthAtMost G x y r ⊕ AvoidingPathOfLengthAtMost G y x r) ≤
      Nat.card V :=
  Nat.card_le_card_of_injective
    (edgeRootAtMostEndpoint (G := G) (x := x) (y := y) (r := r))
    (edgeRootAtMostEndpoint_injective hg hxy hsmall hcross)

abbrev EdgeRootAtMostAsym {V : Type u} (G : SimpleGraph V)
    (x y : V) (r s : ℕ) :=
  AvoidingPathOfLengthAtMost G x y r ⊕ AvoidingPathOfLengthAtMost G y x s

def edgeRootAtMostAsymEndpoint {V : Type u} {G : SimpleGraph V}
    {x y : V} {r s : ℕ} :
    EdgeRootAtMostAsym G x y r s → V
  | Sum.inl A => A.2.1
  | Sum.inr B => B.2.1

theorem edgeRootAtMostAsymEndpoint_injective {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g r s : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hrsmall : r + r < g)
    (hssmall : s + s < g) (hcross : r + (s + 1) < g) :
    Function.Injective
      (edgeRootAtMostAsymEndpoint (G := G) (x := x) (y := y) (r := r) (s := s)) := by
  intro A B h
  cases A with
  | inl A =>
      cases B with
      | inl B =>
          have hAB :
              A = B :=
            avoidingAtMost_endpoint_injective hg (z := x) (forbidden := y) hrsmall h
          cases hAB
          rfl
      | inr B =>
          have hcrossAB : A.1.1 + (B.1.1 + 1) < g := by
            exact Nat.lt_of_le_of_lt (by
              exact Nat.add_le_add A.1.2 (Nat.succ_le_succ B.1.2)) hcross
          exact False.elim
            (edgeRoot_cross_endpoints_ne_lengths hg hxy hcrossAB A.2 B.2 h)
  | inr A =>
      cases B with
      | inl B =>
          have hcrossBA : B.1.1 + (A.1.1 + 1) < g := by
            exact Nat.lt_of_le_of_lt (by
              exact Nat.add_le_add B.1.2 (Nat.succ_le_succ A.1.2)) hcross
          exact False.elim
            (edgeRoot_cross_endpoints_ne_lengths hg hxy hcrossBA B.2 A.2 h.symm)
      | inr B =>
          have hAB :
              A = B :=
            avoidingAtMost_endpoint_injective hg (z := y) (forbidden := x) hssmall h
          cases hAB
          rfl

theorem edgeRootAtMostAsym_card_le_vertices {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r s : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hrsmall : r + r < g)
    (hssmall : s + s < g) (hcross : r + (s + 1) < g) :
    Nat.card (EdgeRootAtMostAsym G x y r s) ≤ Nat.card V :=
  Nat.card_le_card_of_injective
    (edgeRootAtMostAsymEndpoint (G := G) (x := x) (y := y) (r := r) (s := s))
    (edgeRootAtMostAsymEndpoint_injective hg hxy hrsmall hssmall hcross)

abbrev DartRootAvoidingAtMost {V : Type u} (G : SimpleGraph V)
    (d : G.Dart) (r : ℕ) :=
  AvoidingPathOfLengthAtMost G d.toProd.2 d.toProd.1 r ⊕
    AvoidingPathOfLengthAtMost G d.toProd.1 d.toProd.2 r

def dartRootAvoidingEndpoint {V : Type u} {G : SimpleGraph V}
    {d : G.Dart} {r : ℕ} :
    DartRootAvoidingAtMost G d r → V :=
  edgeRootAtMostEndpoint (G := G) (x := d.toProd.2) (y := d.toProd.1) (r := r)

theorem dartRootAvoidingAtMost_card_le_vertices {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hsmall : r + r < g) (hcross : r + (r + 1) < g) :
    Nat.card (DartRootAvoidingAtMost G d r) ≤ Nat.card V := by
  exact edgeRootAtMost_card_le_vertices (G := G) hg d.adj.symm hsmall hcross

abbrev DartRootAvoidingOddAtMost {V : Type u} (G : SimpleGraph V)
    (d : G.Dart) (r : ℕ) :=
  EdgeRootAtMostAsym G d.toProd.2 d.toProd.1 r (r - 1)

def dartRootAvoidingOddEndpoint {V : Type u} {G : SimpleGraph V}
    {d : G.Dart} {r : ℕ} :
    DartRootAvoidingOddAtMost G d r → V :=
  edgeRootAtMostAsymEndpoint (G := G) (x := d.toProd.2) (y := d.toProd.1)
    (r := r) (s := r - 1)

theorem dartRootAvoidingOddAtMost_card_le_vertices {V : Type u} {G : SimpleGraph V}
    [Finite V] [DecidableEq V] {g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    (d : G.Dart) (hrpos : 0 < r) (hsmall : r + r < g) :
    Nat.card (DartRootAvoidingOddAtMost G d r) ≤ Nat.card V := by
  exact edgeRootAtMostAsym_card_le_vertices (G := G) hg d.adj.symm hsmall (by omega) (by omega)

theorem two_mul_two_pow_le_card_of_edgeRoot {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {x y : V} (hxy : G.Adj x y) (hnpos : 0 < n)
    (hsmall : n + n < g) (hcross : n + (n + 1) < g) :
    2 * 2 ^ n ≤ Fintype.card V := by
  let A := AvoidingPathOfLength G x y n
  let B := AvoidingPathOfLength G y x n
  have hleft : 2 ^ n ≤ Nat.card A :=
    two_pow_le_avoidingPath_card G hg hmin hxy hnpos hsmall
  have hright : 2 ^ n ≤ Nat.card B :=
    two_pow_le_avoidingPath_card G hg hmin hxy.symm hnpos hsmall
  have hfiniteA : Finite A :=
    finite_avoidingPathOfLength
      (avoiding_endpoint_injective hg (z := x) (forbidden := y) hsmall)
  have hfiniteB : Finite B :=
    finite_avoidingPathOfLength
      (avoiding_endpoint_injective hg (z := y) (forbidden := x) hsmall)
  letI := hfiniteA
  letI := hfiniteB
  have hsum_lower : 2 ^ n + 2 ^ n ≤ Nat.card (A ⊕ B) := by
    rw [Nat.card_sum]
    exact Nat.add_le_add hleft hright
  have hvertices : Nat.card (A ⊕ B) ≤ Nat.card V :=
    Nat.card_le_card_of_injective
      (edgeRootEndpoint (G := G) (x := x) (y := y) (n := n))
      (edgeRootEndpoint_injective hg hxy hsmall hcross)
  have hsum_vertices : 2 ^ n + 2 ^ n ≤ Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using hsum_lower.trans hvertices
  omega

theorem edgeRootEndpoint_not_surjective {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth)
    {x y : V} (hxy : G.Adj x y) (hnpos : 0 < n)
    (hcross : n + (n + 1) < g) :
    ¬ Function.Surjective
      (edgeRootEndpoint (G := G) (x := x) (y := y) (n := n)) := by
  intro hsurj
  rcases hsurj x with ⟨A, hA⟩
  cases A with
  | inl A =>
      rcases A with ⟨a, p, hp, hplen, havoid⟩
      dsimp [edgeRootEndpoint] at hA
      have hne : x ≠ a :=
        path_start_ne_endpoint_of_pos hp (by
          rw [hplen]
          exact hnpos)
      exact hne hA.symm
  | inr A =>
      rcases A with ⟨a, q, hq, hqlen, havoid⟩
      dsimp [edgeRootEndpoint] at hA
      have hx_not :
          x ∉ q.support :=
        forbidden_not_mem_avoiding_support hg hxy.symm hq hqlen havoid (by omega)
      have hx_mem : x ∈ q.support := by
        have hget : q.getVert q.length = x := by
          rw [SimpleGraph.Walk.getVert_length]
          exact hA
        rw [← hget]
        exact q.getVert_mem_support q.length
      exact hx_not hx_mem

theorem two_mul_two_pow_lt_card_of_edgeRoot {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {x y : V} (hxy : G.Adj x y) (hnpos : 0 < n)
    (hsmall : n + n < g) (hcross : n + (n + 1) < g) :
    2 * 2 ^ n < Fintype.card V := by
  let A := AvoidingPathOfLength G x y n
  let B := AvoidingPathOfLength G y x n
  have hleft : 2 ^ n ≤ Nat.card A :=
    two_pow_le_avoidingPath_card G hg hmin hxy hnpos hsmall
  have hright : 2 ^ n ≤ Nat.card B :=
    two_pow_le_avoidingPath_card G hg hmin hxy.symm hnpos hsmall
  have hfiniteA : Finite A :=
    finite_avoidingPathOfLength
      (avoiding_endpoint_injective hg (z := x) (forbidden := y) hsmall)
  have hfiniteB : Finite B :=
    finite_avoidingPathOfLength
      (avoiding_endpoint_injective hg (z := y) (forbidden := x) hsmall)
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have hsum_lower : 2 ^ n + 2 ^ n ≤ Fintype.card (A ⊕ B) := by
    have hsum : 2 ^ n + 2 ^ n ≤ Nat.card (A ⊕ B) := by
      rw [Nat.card_sum]
      exact Nat.add_le_add hleft hright
    simpa [Nat.card_eq_fintype_card] using hsum
  have hstrict :
      Fintype.card (A ⊕ B) < Fintype.card V :=
    Fintype.card_lt_of_injective_not_surjective
      (edgeRootEndpoint (G := G) (x := x) (y := y) (n := n))
      (edgeRootEndpoint_injective hg hxy hsmall hcross)
      (edgeRootEndpoint_not_surjective hg hxy hnpos hcross)
  have hsum_vertices : 2 ^ n + 2 ^ n < Fintype.card V :=
    lt_of_le_of_lt hsum_lower hstrict
  omega

theorem finite_pathOfLength_of_endpoint_injective {V : Type u} {G : SimpleGraph V}
    [Finite V] {z : V} {n : ℕ}
    (hinj : Function.Injective (fun P : PathOfLength G z n => P.1)) :
    Finite (PathOfLength G z n) :=
  Finite.of_injective (fun P : PathOfLength G z n => P.1) hinj

theorem two_mul_pathOfLength_card_le_succ {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (hsmall : n + n < g) (hnextsmall : (n + 1) + (n + 1) < g) :
    2 * Nat.card (PathOfLength G z n) ≤ Nat.card (PathOfLength G z (n + 1)) := by
  have hinj :=
    twoForwardExtension_injective G hg hmin hnpos hshort hsmall (z := z)
  have htarget_finite : Finite (PathOfLength G z (n + 1)) :=
    finite_pathOfLength_of_endpoint_injective
      (pathOfLength_endpoint_injective hg hnextsmall)
  letI := htarget_finite
  have hcard := Nat.card_le_card_of_injective
    (fun Q : PathOfLength G z n × Fin 2 =>
      twoForwardExtension G hg hmin hnpos hshort Q.1 Q.2)
    hinj
  simpa [Nat.card_prod, Nat.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hcard

theorem d_sub_one_mul_pathOfLength_card_le_succ {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hshort : n + 1 < g)
    (hsmall : n + n < g) (hnextsmall : (n + 1) + (n + 1) < g) :
    (d - 1) * Nat.card (PathOfLength G z n) ≤
      Nat.card (PathOfLength G z (n + 1)) := by
  have hinj :=
    dForwardExtension_injective G hg hmin hnpos hshort hsmall (z := z)
  have htarget_finite : Finite (PathOfLength G z (n + 1)) :=
    finite_pathOfLength_of_endpoint_injective
      (pathOfLength_endpoint_injective hg hnextsmall)
  letI := htarget_finite
  have hcard := Nat.card_le_card_of_injective
    (fun Q : PathOfLength G z n × Fin (d - 1) =>
      dForwardExtension G hg hmin hnpos hshort Q.1 Q.2)
    hinj
  simpa [Nat.card_prod, Nat.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hcard

theorem pathOfLength_card_le_vertices {V : Type u} {G : SimpleGraph V} [Finite V]
    {z : V} {n : ℕ}
    (hinj : Function.Injective (fun P : PathOfLength G z n => P.1)) :
    Nat.card (PathOfLength G z n) ≤ Nat.card V :=
  Nat.card_le_card_of_injective (fun P : PathOfLength G z n => P.1) hinj

theorem degree_le_pathOfLength_one {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] (z : V) [Finite (PathOfLength G z 1)] :
    G.degree z ≤ Nat.card (PathOfLength G z 1) := by
  classical
  let f : G.neighborSet z → PathOfLength G z 1 := fun w =>
    let hAdj : G.Adj z w.1 := (SimpleGraph.mem_neighborSet G z w.1).mp w.2
    ⟨w.1, ⟨SimpleGraph.Walk.cons hAdj SimpleGraph.Walk.nil,
      by
        constructor
        · rw [SimpleGraph.Walk.isPath_def]
          simp [SimpleGraph.Walk.support_cons, hAdj.ne]
        · simp⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun P : PathOfLength G z 1 => P.1) hab)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hcard
  exact hcard

theorem d_mul_pow_pred_le_pathOfLength_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hd : 2 ≤ d) (hnpos : 0 < n) (hsmall : n + n < g) :
    d * (d - 1) ^ (n - 1) ≤ Nat.card (PathOfLength G z n) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          have hinj1 : Function.Injective (fun P : PathOfLength G z 1 => P.1) :=
            pathOfLength_endpoint_injective hg hsmall
          have hfinite1 : Finite (PathOfLength G z 1) :=
            finite_pathOfLength_of_endpoint_injective hinj1
          letI := hfinite1
          have hdeg_le : G.degree z ≤ Nat.card (PathOfLength G z 1) :=
            degree_le_pathOfLength_one G z
          have hmin_le : d ≤ G.degree z := hmin.trans (G.minDegree_le_degree z)
          norm_num
          exact hmin_le.trans hdeg_le
      | succ m =>
          have hmpos : 0 < m + 1 := by omega
          have hsmall_m : (m + 1) + (m + 1) < g := by omega
          have ih_m :
              d * (d - 1) ^ ((m + 1) - 1) ≤ Nat.card (PathOfLength G z (m + 1)) :=
            ih (by omega) hsmall_m
          rw [show (m + 1) - 1 = m by omega] at ih_m
          have hshort : (m + 1) + 1 < g := by omega
          have hrec :
              (d - 1) * Nat.card (PathOfLength G z (m + 1)) ≤
                Nat.card (PathOfLength G z ((m + 1) + 1)) :=
            d_sub_one_mul_pathOfLength_card_le_succ G hg hmin hmpos hshort hsmall_m hsmall
          have hmul :
              (d - 1) * (d * (d - 1) ^ m) ≤
                Nat.card (PathOfLength G z ((m + 1) + 1)) :=
            (Nat.mul_le_mul_left (d - 1) ih_m).trans hrec
          have hleft :
              d * (d - 1) ^ (((m + 1) + 1) - 1) =
                (d - 1) * (d * (d - 1) ^ m) := by
            rw [show ((m + 1) + 1) - 1 = m + 1 by omega, pow_succ]
            rw [← Nat.mul_assoc]
            rw [Nat.mul_comm (d * (d - 1) ^ m) (d - 1)]
          rw [hleft]
          exact hmul

theorem d_mul_pow_pred_le_card_of_minDegree_girth {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hd : 2 ≤ d) (hnpos : 0 < n) (hsmall : n + n < g) :
    d * (d - 1) ^ (n - 1) ≤ Fintype.card V := by
  have hpaths :=
    d_mul_pow_pred_le_pathOfLength_card G hg hmin hd hnpos hsmall (z := z)
  have hvertices : Nat.card (PathOfLength G z n) ≤ Nat.card V :=
    pathOfLength_card_le_vertices (pathOfLength_endpoint_injective hg hsmall)
  simpa [Nat.card_eq_fintype_card] using hpaths.trans hvertices

theorem d_moore_odd_sum_le_card_of_minDegree_girth {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {d g r : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : d ≤ G.minDegree)
    {z : V} (hd : 2 ≤ d) (hsmall : r + r < g) :
    1 + (∑ i : Fin r, d * (d - 1) ^ (i : ℕ)) ≤ Fintype.card V := by
  letI : Fintype {n : ℕ // n ≤ r} :=
    Fintype.ofEquiv (Fin (r + 1)) (leNatSubtypeEquivFin r).symm
  letI : ∀ n : {n : ℕ // n ≤ r}, Finite (PathOfLength G z n.1) := fun n =>
    finite_pathOfLength_of_endpoint_injective
      (pathOfLength_endpoint_injective hg (by omega))
  have hzero : 1 ≤ Nat.card (PathOfLength G z 0) := by
    have hfinite0 : Finite (PathOfLength G z 0) :=
      finite_pathOfLength_of_endpoint_injective
        (pathOfLength_endpoint_injective hg (by omega))
    letI := hfinite0
    let f : Unit → PathOfLength G z 0 := fun _ =>
      ⟨z, ⟨SimpleGraph.Walk.nil,
        by
          constructor
          · simp [SimpleGraph.Walk.isPath_def]
          · simp⟩⟩
    have hf : Function.Injective f := by
      intro a b _
      cases a
      cases b
      rfl
    have hcard := Nat.card_le_card_of_injective f hf
    simpa using hcard
  have hterm :
      ∀ n : {n : ℕ // n ≤ r},
        (if n.1 = 0 then 1 else d * (d - 1) ^ (n.1 - 1)) ≤
          Nat.card (PathOfLength G z n.1) := by
    intro n
    by_cases hn0 : n.1 = 0
    · simpa [hn0] using hzero
    · have hnpos : 0 < n.1 := by omega
      have hsmall_n : n.1 + n.1 < g := by omega
      simpa [hn0] using
        d_mul_pow_pred_le_pathOfLength_card G hg hmin hd hnpos hsmall_n (z := z)
  have hsum_lower :
      (∑ n : {n : ℕ // n ≤ r},
        if n.1 = 0 then 1 else d * (d - 1) ^ (n.1 - 1)) ≤
        Nat.card (PathOfLengthAtMost G z r) := by
    have hle :
        (∑ n : {n : ℕ // n ≤ r},
          if n.1 = 0 then 1 else d * (d - 1) ^ (n.1 - 1)) ≤
          ∑ n : {n : ℕ // n ≤ r}, Nat.card (PathOfLength G z n.1) :=
      Finset.sum_le_sum (by
        intro n _
        exact hterm n)
    have hsigma :
        Nat.card (PathOfLengthAtMost G z r) =
          ∑ n : {n : ℕ // n ≤ r}, Nat.card (PathOfLength G z n.1) := by
      exact Nat.card_sigma
    rwa [← hsigma] at hle
  have hsum_reindex :
      (∑ n : {n : ℕ // n ≤ r},
        if n.1 = 0 then 1 else d * (d - 1) ^ (n.1 - 1)) =
        1 + ∑ i : Fin r, d * (d - 1) ^ (i : ℕ) := by
    rw [Fintype.sum_equiv (leNatSubtypeEquivFin r)
      (fun n : {n : ℕ // n ≤ r} =>
        if n.1 = 0 then 1 else d * (d - 1) ^ (n.1 - 1))
      (fun i : Fin (r + 1) =>
        if (i : ℕ) = 0 then 1 else d * (d - 1) ^ ((i : ℕ) - 1))
      (by intro x; rfl)]
    rw [Fin.sum_univ_succ]
    simp
  have hvertices : Nat.card (PathOfLengthAtMost G z r) ≤ Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using
      pathAtMost_card_le_vertices (pathAtMost_endpoint_injective hg hsmall)
  rw [hsum_reindex] at hsum_lower
  exact hsum_lower.trans hvertices

theorem two_pow_le_pathOfLength_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hsmall : n + n < g) :
    2 ^ n ≤ Nat.card (PathOfLength G z n) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          have hinj1 : Function.Injective (fun P : PathOfLength G z 1 => P.1) :=
            pathOfLength_endpoint_injective hg hsmall
          have hfinite1 : Finite (PathOfLength G z 1) :=
            finite_pathOfLength_of_endpoint_injective hinj1
          letI := hfinite1
          have hdeg_le : G.degree z ≤ Nat.card (PathOfLength G z 1) :=
            degree_le_pathOfLength_one G z
          have hmin_le : 3 ≤ G.degree z := hmin.trans (G.minDegree_le_degree z)
          norm_num
          omega
      | succ m =>
          have hmpos : 0 < m + 1 := by omega
          have hsmall_m : (m + 1) + (m + 1) < g := by omega
          have ih_m : 2 ^ (m + 1) ≤ Nat.card (PathOfLength G z (m + 1)) :=
            ih (by omega) hsmall_m
          have hshort : (m + 1) + 1 < g := by omega
          have hrec :
              2 * Nat.card (PathOfLength G z (m + 1)) ≤
                Nat.card (PathOfLength G z ((m + 1) + 1)) :=
            two_mul_pathOfLength_card_le_succ G hg hmin hmpos hshort hsmall_m hsmall
          rw [pow_succ]
          rw [Nat.mul_comm (2 ^ (m + 1)) 2]
          exact (Nat.mul_le_mul_left 2 ih_m).trans hrec

theorem three_mul_two_pow_pred_le_pathOfLength_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hsmall : n + n < g) :
    3 * 2 ^ (n - 1) ≤ Nat.card (PathOfLength G z n) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          have hinj1 : Function.Injective (fun P : PathOfLength G z 1 => P.1) :=
            pathOfLength_endpoint_injective hg hsmall
          have hfinite1 : Finite (PathOfLength G z 1) :=
            finite_pathOfLength_of_endpoint_injective hinj1
          letI := hfinite1
          have hdeg_le : G.degree z ≤ Nat.card (PathOfLength G z 1) :=
            degree_le_pathOfLength_one G z
          have hmin_le : 3 ≤ G.degree z := hmin.trans (G.minDegree_le_degree z)
          norm_num
          omega
      | succ m =>
          have hmpos : 0 < m + 1 := by omega
          have hsmall_m : (m + 1) + (m + 1) < g := by omega
          have ih_m :
              3 * 2 ^ ((m + 1) - 1) ≤ Nat.card (PathOfLength G z (m + 1)) :=
            ih (by omega) hsmall_m
          rw [show (m + 1) - 1 = m by omega] at ih_m
          have hshort : (m + 1) + 1 < g := by omega
          have hrec :
              2 * Nat.card (PathOfLength G z (m + 1)) ≤
                Nat.card (PathOfLength G z ((m + 1) + 1)) :=
            two_mul_pathOfLength_card_le_succ G hg hmin hmpos hshort hsmall_m hsmall
          have hmul :
              2 * (3 * 2 ^ m) ≤ Nat.card (PathOfLength G z ((m + 1) + 1)) :=
            (Nat.mul_le_mul_left 2 ih_m).trans hrec
          have hleft :
              3 * 2 ^ (((m + 1) + 1) - 1) = 2 * (3 * 2 ^ m) := by
            rw [show ((m + 1) + 1) - 1 = m + 1 by omega, pow_succ]
            rw [← Nat.mul_assoc]
            rw [Nat.mul_comm (3 * 2 ^ m) 2]
          rw [hleft]
          exact hmul

theorem three_mul_two_pow_pred_le_card_of_minDegree_girth {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hsmall : n + n < g) :
    3 * 2 ^ (n - 1) ≤ Fintype.card V := by
  have hpaths :=
    three_mul_two_pow_pred_le_pathOfLength_card G hg hmin hnpos hsmall (z := z)
  have hvertices : Nat.card (PathOfLength G z n) ≤ Nat.card V :=
    pathOfLength_card_le_vertices (pathOfLength_endpoint_injective hg hsmall)
  simpa [Nat.card_eq_fintype_card] using hpaths.trans hvertices

theorem two_pow_le_card_of_minDegree_girth {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {g n : ℕ} (hg : (g : ℕ∞) ≤ G.egirth) (hmin : 3 ≤ G.minDegree)
    {z : V} (hnpos : 0 < n) (hsmall : n + n < g) :
    2 ^ n ≤ Fintype.card V := by
  have hpaths := two_pow_le_pathOfLength_card G hg hmin hnpos hsmall (z := z)
  have hvertices : Nat.card (PathOfLength G z n) ≤ Nat.card V :=
    pathOfLength_card_le_vertices (pathOfLength_endpoint_injective hg hsmall)
  simpa [Nat.card_eq_fintype_card] using hpaths.trans hvertices

end Chapter01
end Diestel
