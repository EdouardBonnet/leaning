import Chapter01.cycle_space_even_support
import Chapter01.cycle_space_list_repr

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

private def selectedEdges {V : Type u} {G : SimpleGraph V} (D : EdgeSpace G) :
    Set G.edgeSet :=
  {e | D e = 1}

private lemma zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl
  · rfl
  · change (2 : ZMod 2) = 0
    exact ZMod.natCast_self 2

private lemma zmod_two_eq_zero_of_ne_one (x : ZMod 2) (h : ¬ x = 1) : x = 0 := by
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with hx | hx
  · exact hx
  · exact False.elim (h hx)

private lemma exists_edge_of_isCycle {V : Type u} {G : SimpleGraph V} {a : V}
    {c : G.Walk a a} (hc : c.IsCycle) :
    ∃ e : G.edgeSet, (e : Sym2 V) ∈ c.edgeSet := by
  have hlen : 3 ≤ c.length :=
    (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mp hc).2
  cases c with
  | nil =>
      simp at hlen
  | cons h p =>
      rename_i b
      refine ⟨⟨s(a, b), ?_⟩, ?_⟩
      · rw [SimpleGraph.mem_edgeSet]
        exact h
      · rw [SimpleGraph.Walk.mem_edgeSet]
        simp [SimpleGraph.Walk.edges_cons]

private lemma incidence_sum_add {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] (D E : EdgeSpace G) (v : V) :
    (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then (D + E) e else 0)) =
      (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then D e else 0)) +
        ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then E e else 0) := by
  classical
  calc
    (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then (D + E) e else 0))
        =
      ∑ e : G.edgeSet,
        ((if v ∈ (e : Sym2 V) then D e else 0) +
          (if v ∈ (e : Sym2 V) then E e else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro e _he
        by_cases hv : v ∈ (e : Sym2 V) <;> simp [hv]
    _ =
      (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then D e else 0)) +
        ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then E e else 0) := by
        rw [Finset.sum_add_distrib]

private lemma even_incidence_add {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {D E : EdgeSpace G}
    (hD : ∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)}))
    (hE : ∀ v : V, Even (Nat.card {e : G.edgeSet // E e = 1 ∧ v ∈ (e : Sym2 V)})) :
    ∀ v : V, Even (Nat.card {e : G.edgeSet // (D + E) e = 1 ∧ v ∈ (e : Sym2 V)}) := by
  intro v
  have hsumD := (even_incidence_iff_sum_zero D v).mp (hD v)
  have hsumE := (even_incidence_iff_sum_zero E v).mp (hE v)
  exact (even_incidence_iff_sum_zero (D + E) v).mpr (by
    rw [incidence_sum_add D E v, hsumD, hsumE, add_zero])

private lemma cycle_vector_mem_cycle_space {V : Type u} {G : SimpleGraph V}
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) :
    cycle_vector G c ∈ cycle_space G :=
  Submodule.subset_span ⟨a, c, hc, rfl⟩

private lemma selected_subset_after_delete_cycle {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] {D : EdgeSpace G} {a : V} {c : G.Walk a a}
    (hselected : ∀ e : G.edgeSet, (e : Sym2 V) ∈ c.edgeSet → D e = 1) :
    selectedEdges (D + cycle_vector G c) ⊆ selectedEdges D := by
  classical
  intro e he
  by_cases hec : (e : Sym2 V) ∈ c.edgeSet
  · exact hselected e hec
  · have hcv : cycle_vector G c e = 0 := by
      simp [cycle_vector, hec]
    dsimp [selectedEdges] at he ⊢
    simpa [hcv] using he

private lemma selected_card_lt_after_delete_cycle {V : Type u} {G : SimpleGraph V}
    [Fintype G.edgeSet] {D : EdgeSpace G} {a : V} {c : G.Walk a a}
    (hc : c.IsCycle)
    (hselected : ∀ e : G.edgeSet, (e : Sym2 V) ∈ c.edgeSet → D e = 1) :
    Fintype.card {e : G.edgeSet // (D + cycle_vector G c) e = 1} <
      Fintype.card {e : G.edgeSet // D e = 1} := by
  classical
  let D' : EdgeSpace G := D + cycle_vector G c
  have hsubset : selectedEdges D' ⊆ selectedEdges D := by
    simpa [D'] using selected_subset_after_delete_cycle (D := D) (c := c) hselected
  obtain ⟨e₀, he₀c⟩ := exists_edge_of_isCycle hc
  have he₀D : D e₀ = 1 := hselected e₀ he₀c
  have he₀cv : cycle_vector G c e₀ = 1 := by
    simp [cycle_vector, he₀c]
  have he₀D'zero : D' e₀ = 0 := by
    dsimp [D']
    rw [he₀D, he₀cv]
    change (1 : ZMod 2) + 1 = 0
    exact zmod_two_add_self 1
  let f : {e : G.edgeSet // D' e = 1} → {e : G.edgeSet // D e = 1} :=
    fun e => ⟨e.1, hsubset e.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun e : {e : G.edgeSet // D e = 1} => (e : G.edgeSet)) hxy
  have hnot_range : (⟨e₀, he₀D⟩ : {e : G.edgeSet // D e = 1}) ∉ Set.range f := by
    rintro ⟨e, heq⟩
    have hval : e.1 = e₀ :=
      congrArg (fun e : {e : G.edgeSet // D e = 1} => (e : G.edgeSet)) heq
    have heD' : D' e₀ = 1 := by
      simpa [hval] using e.2
    rw [he₀D'zero] at heD'
    exact zero_ne_one heD'
  exact Fintype.card_lt_of_injective_of_notMem f hf hnot_range

private theorem cycle_space_of_even_incidence_aux {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] :
    ∀ n : ℕ, ∀ D : EdgeSpace G,
      Fintype.card {e : G.edgeSet // D e = 1} = n →
        (∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)})) →
          D ∈ cycle_space G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro D hcard hD
      by_cases hnonzero : ∃ e : G.edgeSet, D e = 1
      · obtain ⟨a, cH, hcH⟩ :=
          supportGraph_exists_cycle_of_nonzero_even G D hnonzero hD
        obtain ⟨c, hc, hselected⟩ :=
          supportGraph_cycle_transfers_to_selected_cycle G D cH hcH
        let D' : EdgeSpace G := D + cycle_vector G c
        have hD'even : ∀ v : V,
            Even (Nat.card {e : G.edgeSet // D' e = 1 ∧ v ∈ (e : Sym2 V)}) := by
          dsimp [D']
          exact even_incidence_add hD (cycle_vector_even_incidence c hc)
        have hlt : Fintype.card {e : G.edgeSet // D' e = 1} < n := by
          rw [← hcard]
          exact selected_card_lt_after_delete_cycle (D := D) (c := c) hc hselected
        have hD'mem : D' ∈ cycle_space G :=
          ih (Fintype.card {e : G.edgeSet // D' e = 1}) hlt D' rfl hD'even
        have hcmem : cycle_vector G c ∈ cycle_space G :=
          cycle_vector_mem_cycle_space c hc
        have hsum : cycle_vector G c + D' = D := by
          ext e
          dsimp [D']
          calc
            cycle_vector G c e + (D e + cycle_vector G c e)
                = D e + (cycle_vector G c e + cycle_vector G c e) := by
              rw [add_comm (cycle_vector G c e) (D e + cycle_vector G c e), add_assoc]
            _ = D e + 0 := by
              rw [zmod_two_add_self]
            _ = D e := by rw [add_zero]
        rw [← hsum]
        exact Submodule.add_mem (cycle_space G) hcmem hD'mem
      · have hzero : D = 0 := by
          ext e
          by_cases hDe : D e = 1
          · exact False.elim (hnonzero ⟨e, hDe⟩)
          · exact zmod_two_eq_zero_of_ne_one (D e) hDe
        rw [hzero]
        exact Submodule.zero_mem (cycle_space G)

private theorem cycle_space_of_even_incidence {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet] {D : EdgeSpace G}
    (hD : ∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)})) :
    D ∈ cycle_space G :=
  cycle_space_of_even_incidence_aux G
    (Fintype.card {e : G.edgeSet // D e = 1}) D rfl hD

/--
Diestel, Proposition 1.9.1.
Cycle-space membership is equivalent to a finite sum of cycles and to even
degree at every vertex of the selected-edge subgraph.
-/
theorem proposition_1_9_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    (D : EdgeSpace G) :
    (D ∈ cycle_space G ↔
      ∃ cycles : List (Σ a : V, G.Walk a a),
        (∀ c ∈ cycles, c.2.IsCycle) ∧
          D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0) ∧
      (D ∈ cycle_space G ↔
        ∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)})) := by
  exact ⟨cycle_space_list_repr G D,
    ⟨fun h v => cycle_space_even_incidence h v,
      fun h => cycle_space_of_even_incidence G h⟩⟩

end Chapter01
end Diestel
