import Chapter01.definitions_ch1
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

private lemma isCycle_isTrail {V : Type u} {G : SimpleGraph V} {a : V}
    {c : G.Walk a a} (hc : c.IsCycle) : c.IsTrail := by
  cases c with
  | nil =>
      simp [SimpleGraph.Walk.isTrail_def]
  | cons h p =>
      rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
      rw [SimpleGraph.Walk.isTrail_cons]
      exact ⟨hc.1.isTrail, hc.2⟩

private lemma cycle_list_repr_zero {V : Type u} (G : SimpleGraph V) :
    ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        (0 : EdgeSpace G) = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0 := by
  exact ⟨[], by simp, by simp⟩

private lemma cycle_list_repr_add {V : Type u} (G : SimpleGraph V)
    {D E : EdgeSpace G}
    (hD : ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0)
    (hE : ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        E = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0) :
    ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        D + E = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0 := by
  rcases hD with ⟨cyclesD, hcyclesD, rfl⟩
  rcases hE with ⟨cyclesE, hcyclesE, rfl⟩
  refine ⟨cyclesD ++ cyclesE, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcyclesD c hc
    · exact hcyclesE c hc
  · induction cyclesD with
    | nil =>
        simp
    | cons c cs ih =>
        have htail : ∀ d ∈ cs, d.2.IsCycle := by
          intro d hd
          exact hcyclesD d (by simp [hd])
        have ih' := ih htail
        simp only [List.foldr_cons]
        rw [add_assoc]
        rw [ih']
        rfl

private lemma cycle_list_repr_smul {V : Type u} (G : SimpleGraph V) (a : ZMod 2)
    {D : EdgeSpace G}
    (hD : ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0) :
    ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        a • D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0 := by
  fin_cases a
  · rcases cycle_list_repr_zero G with ⟨cycles, hcycles, hzero⟩
    refine ⟨cycles, hcycles, ?_⟩
    change (0 : ZMod 2) • D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0
    rw [zero_smul]
    exact hzero
  · rcases hD with ⟨cycles, hcycles, hD⟩
    refine ⟨cycles, hcycles, ?_⟩
    change (1 : ZMod 2) • D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0
    rw [one_smul]
    exact hD

private lemma cycle_list_repr_mem_cycle_space {V : Type u} (G : SimpleGraph V)
    {D : EdgeSpace G}
    (hD : ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0) :
    D ∈ cycle_space G := by
  classical
  rcases hD with ⟨cycles, hcycles, rfl⟩
  induction cycles with
  | nil =>
      simp [cycle_space]
  | cons c cs ih =>
      have hc : cycle_vector G c.2 ∈ cycle_space G := by
        exact Submodule.subset_span ⟨c.1, c.2, hcycles c (by simp), rfl⟩
      have hcs : (cs.foldr (fun c acc => cycle_vector G c.2 + acc) 0) ∈ cycle_space G := by
        apply ih
        intro d hd
        exact hcycles d (by simp [hd])
      simpa using Submodule.add_mem (cycle_space G) hc hcs

/--
Membership in the cycle space is equivalent to being a finite sum of cycle
vectors.
-/
theorem cycle_space_list_repr {V : Type u} (G : SimpleGraph V) (D : EdgeSpace G) :
    D ∈ cycle_space G ↔
      ∃ cycles : List (Σ a : V, G.Walk a a),
        (∀ c ∈ cycles, c.2.IsCycle) ∧
          D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0 := by
  constructor
  · intro hD
    change D ∈
      Submodule.span (ZMod 2)
        {F : EdgeSpace G | ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ F = cycle_vector G c} at hD
    induction hD using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨a, c, hc, rfl⟩
        refine ⟨[⟨a, c⟩], ?_, by simp⟩
        intro d hd
        simp only [List.mem_singleton] at hd
        subst d
        exact hc
    | zero =>
        exact cycle_list_repr_zero G
    | add x y _ _ hx hy =>
        exact cycle_list_repr_add G hx hy
    | smul a x _ hx =>
        exact cycle_list_repr_smul G a hx
  · exact cycle_list_repr_mem_cycle_space G

private noncomputable def cycleIncidentEdges {V : Type u} {G : SimpleGraph V}
    [DecidableEq V] {a : V} (c : G.Walk a a) (v : V) : Finset (Sym2 V) :=
  (c.edges.filter fun e => decide (v ∈ e)).toFinset

private lemma cycleIncidentEdges_card_eq_countP {V : Type u} {G : SimpleGraph V}
    {a v : V} [DecidableEq V] {c : G.Walk a a} (hc : c.IsCycle) :
    (cycleIncidentEdges c v).card =
      c.edges.countP (fun e => decide (v ∈ e)) := by
  have htrail : c.IsTrail := isCycle_isTrail hc
  rw [cycleIncidentEdges, List.countP_eq_length_filter,
    List.toFinset_card_of_nodup]
  exact htrail.edges_nodup.filter _

private lemma cycle_vector_incidence_card_eq_countP {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] {a v : V} [DecidableEq V] {c : G.Walk a a} (hc : c.IsCycle) :
    Nat.card {e : G.edgeSet // cycle_vector G c e = 1 ∧ v ∈ (e : Sym2 V)} =
      c.edges.countP (fun e => decide (v ∈ e)) := by
  classical
  let S := {e : G.edgeSet // cycle_vector G c e = 1 ∧ v ∈ (e : Sym2 V)}
  let R : Set (Sym2 V) := {e | e ∈ c.edges ∧ v ∈ e}
  let F := cycleIncidentEdges c v
  have hF_mem : ∀ e : Sym2 V, e ∈ F ↔ e ∈ R := by
    intro e
    constructor
    · intro he
      have he' := he
      dsimp [F, R, cycleIncidentEdges] at he'
      have hf : e ∈ c.edges ∧ decide (v ∈ e) = true := by
        simpa using List.mem_toFinset.mp he'
      exact ⟨hf.1, of_decide_eq_true hf.2⟩
    · intro he
      dsimp [F, R, cycleIncidentEdges] at he ⊢
      exact List.mem_toFinset.mpr (by
        rw [List.mem_filter]
        exact ⟨he.1, decide_eq_true he.2⟩)
  letI : Fintype R := Fintype.ofFinset F hF_mem
  have hcardS : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  have hSR : Fintype.card S = Fintype.card R := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun e => ⟨(e.1 : Sym2 V), ?_⟩
        invFun := fun e => ⟨⟨e.1, c.edges_subset_edgeSet e.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hvec := e.2.1
      by_contra hnot
      have hnot_edges : (e.1 : Sym2 V) ∉ c.edges := by
        intro he_edges
        exact hnot ⟨he_edges, e.2.2⟩
      have hzero : cycle_vector G c e.1 = 0 := by
        simp [cycle_vector, SimpleGraph.Walk.mem_edgeSet, hnot_edges]
      rw [hzero] at hvec
      norm_num at hvec
    · exact ⟨by simp [cycle_vector, SimpleGraph.Walk.mem_edgeSet.mpr e.2.1], e.2.2⟩
    · intro e
      rfl
    · intro e
      rfl
  have hcardF : F.card = Fintype.card R := by
    exact (Fintype.card_ofFinset F hF_mem).symm
  rw [hcardS, hSR, ← hcardF, cycleIncidentEdges_card_eq_countP hc]

/-- A cycle vector has even incidence at every vertex. -/
theorem cycle_vector_even_incidence {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] {a : V} (c : G.Walk a a) (hc : c.IsCycle) (v : V) :
    Even (Nat.card {e : G.edgeSet // cycle_vector G c e = 1 ∧ v ∈ (e : Sym2 V)}) := by
  classical
  rw [cycle_vector_incidence_card_eq_countP hc]
  have htrail : c.IsTrail := isCycle_isTrail hc
  exact (htrail.even_countP_edges_iff v).mpr (by
    intro hne
    exact False.elim (hne rfl))

private lemma zmod_two_natCast_eq_zero_iff_even (n : ℕ) :
    (n : ZMod 2) = 0 ↔ Even n := by
  rw [CharP.cast_eq_zero_iff (ZMod 2) 2 n]
  exact Iff.symm even_iff_two_dvd

private lemma zmod_two_eq_zero_of_ne_one (z : ZMod 2) (h : ¬ z = 1) : z = 0 := by
  fin_cases z
  · rfl
  · exfalso
    exact h rfl

/-- The mod-2 incidence sum counts incident `1`-edges modulo two. -/
theorem incidence_sum_eq_card_ones {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] (F : EdgeSpace G) (v : V) :
    (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then F e else 0)) =
      (Nat.card {e : G.edgeSet // F e = 1 ∧ v ∈ (e : Sym2 V)} : ZMod 2) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_boole (fun e : G.edgeSet => F e = 1 ∧ v ∈ (e : Sym2 V)) Finset.univ]
  refine Finset.sum_congr rfl ?_
  intro e _he
  by_cases hv : v ∈ (e : Sym2 V)
  · by_cases hF : F e = 1
    · simp [hv, hF]
    · have hzero : F e = 0 := by
        exact zmod_two_eq_zero_of_ne_one (F e) hF
      simp [hv, hF, hzero]
  · simp [hv]

theorem even_incidence_iff_sum_zero {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] (F : EdgeSpace G) (v : V) :
    Even (Nat.card {e : G.edgeSet // F e = 1 ∧ v ∈ (e : Sym2 V)}) ↔
      (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then F e else 0)) = 0 := by
  rw [incidence_sum_eq_card_ones F v]
  exact (zmod_two_natCast_eq_zero_iff_even _).symm

theorem cycle_space_incidence_sum_zero {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {D : EdgeSpace G}
    (hD : D ∈ cycle_space G) (v : V) :
    (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then D e else 0)) = 0 := by
  classical
  change D ∈
      Submodule.span (ZMod 2)
        {F : EdgeSpace G | ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ F = cycle_vector G c} at hD
  induction hD using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨a, c, hc, rfl⟩
      exact (even_incidence_iff_sum_zero (cycle_vector G c) v).mp
        (cycle_vector_even_incidence c hc v)
  | zero =>
      simp
  | add x y _ _ hx hy =>
      calc
        (∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then x e + y e else 0)
            =
          ∑ e : G.edgeSet,
            ((if v ∈ (e : Sym2 V) then x e else 0) +
              (if v ∈ (e : Sym2 V) then y e else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e _he
            by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
        _ =
          (∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then x e else 0) +
            ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then y e else 0 := by
            rw [Finset.sum_add_distrib]
        _ = 0 := by rw [hx, hy, add_zero]
  | smul a x _ hx =>
      fin_cases a
      · refine Finset.sum_eq_zero ?_
        intro e _he
        by_cases hv : v ∈ (e : Sym2 V)
        · rw [if_pos hv]
          exact zero_mul (x e)
        · simp [hv]
      · calc
          (∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then 1 * x e else 0)
              =
            ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then x e else 0 := by
              refine Finset.sum_congr rfl ?_
              intro e _he
              by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
          _ = 0 := hx

theorem cycle_space_even_incidence {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {D : EdgeSpace G}
    (hD : D ∈ cycle_space G) (v : V) :
    Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)}) :=
  (even_incidence_iff_sum_zero D v).mpr (cycle_space_incidence_sum_zero hD v)

end Chapter01
end Diestel
