import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.Linarith

set_option linter.all false

open SimpleGraph

universe u

namespace Diestel
namespace Chapter01

private lemma tail_length_eq_sub_one {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : p.tail.length = p.length - 1 := by
  by_cases hp : p.Nil
  · have hp_len : p.length = 0 := SimpleGraph.Walk.nil_iff_length_eq.mp hp
    have htail_len : p.tail.length = 0 := SimpleGraph.Walk.nil_iff_length_eq.mp hp.tail
    omega
  · have h := SimpleGraph.Walk.length_tail_add_one (p := p) hp
    omega

private lemma repeated_positions_of_not_cycle_of_odd {V : Type u} {G : SimpleGraph V} {a : V}
    (w : G.Walk a a) (hnotcycle : ¬ w.IsCycle) (hodd : Odd w.length) :
    ∃ i j : ℕ, 0 < i ∧ i < j ∧ j ≤ w.length ∧ w.getVert i = w.getVert j := by
  have hne0 : w.length ≠ 0 := by
    intro h0
    exact Nat.not_odd_zero (h0 ▸ hodd)
  have hne1 : w.length ≠ 1 := by
    intro h1
    have hadj : G.Adj a a := SimpleGraph.Walk.adj_of_length_eq_one (p := w) h1
    exact SimpleGraph.irrefl G hadj
  have hge3 : 3 ≤ w.length := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hnot_tail_path : ¬ w.tail.IsPath := by
    intro hp
    exact hnotcycle (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨hp, hge3⟩)
  have hnot_nodup : ¬ w.tail.support.Nodup := by
    intro hs
    exact hnot_tail_path ((SimpleGraph.Walk.isPath_def w.tail).mpr hs)
  obtain ⟨x, hxdup⟩ := (List.exists_duplicate_iff_not_nodup).2 hnot_nodup
  obtain ⟨i, j, hij, hxi, hxj⟩ := (List.duplicate_iff_exists_distinct_get).1 hxdup
  have hi_tail : (i : ℕ) ≤ w.tail.length := by
    have hi_lt : (i : ℕ) < w.tail.length + 1 := by
      simpa [SimpleGraph.Walk.length_support] using i.2
    omega
  have hj_tail : (j : ℕ) ≤ w.tail.length := by
    have hj_lt : (j : ℕ) < w.tail.length + 1 := by
      simpa [SimpleGraph.Walk.length_support] using j.2
    omega
  have hxi_vert : x = w.tail.getVert i := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem w.tail hi_tail]
    exact hxi
  have hxj_vert : x = w.tail.getVert j := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem w.tail hj_tail]
    exact hxj
  have hget : w.getVert ((i : ℕ) + 1) = w.getVert ((j : ℕ) + 1) := by
    have htailget : w.tail.getVert i = w.tail.getVert j := hxi_vert.symm.trans hxj_vert
    simpa [SimpleGraph.Walk.getVert_tail] using htailget
  refine ⟨(i : ℕ) + 1, (j : ℕ) + 1, by omega, ?_, ?_, hget⟩
  · have hijNat : (i : ℕ) < (j : ℕ) := hij
    omega
  · rw [tail_length_eq_sub_one w] at hj_tail
    omega

private theorem odd_closed_walk_contains_odd_cycle {V : Type u} {G : SimpleGraph V} :
    ∀ {a : V} (w : G.Walk a a), Odd w.length →
      ∃ b : V, ∃ c : G.Walk b b, c.IsCycle ∧ Odd c.length := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {a : V} (w : G.Walk a a), w.length = n → Odd w.length →
      ∃ b : V, ∃ c : G.Walk b b, c.IsCycle ∧ Odd c.length
  have aux : ∀ n : ℕ, P n := by
    intro n
    exact Nat.strong_induction_on (p := P) n (by
      intro n ih a w hwlen hodd
      by_cases hcycle : w.IsCycle
      · exact ⟨a, w, hcycle, hodd⟩
      · obtain ⟨i, j, hi_pos, hij, hj_le, hget⟩ :=
          repeated_positions_of_not_cycle_of_odd w hcycle hodd
        let seg : G.Walk (w.getVert i) (w.getVert i) :=
          ((w.drop i).take (j - i)).copy rfl (by
            rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij.le]
            exact hget.symm)
        let comp : G.Walk a a :=
          (w.take i).append ((w.drop j).copy hget.symm rfl)
        have hi_le : i ≤ w.length := le_trans hij.le hj_le
        have hseg_len : seg.length = j - i := by
          dsimp [seg]
          simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
            SimpleGraph.Walk.drop_length]
          have hle : j - i ≤ w.length - i := Nat.sub_le_sub_right hj_le i
          rw [Nat.min_eq_left hle]
        have hcomp_len : comp.length = i + (w.length - j) := by
          dsimp [comp]
          simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
            SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
          rw [Nat.min_eq_left hi_le]
        have hsum : w.length = seg.length + comp.length := by
          rw [hseg_len, hcomp_len]
          omega
        by_cases hseg_odd : Odd seg.length
        · have hseg_lt : seg.length < n := by
            rw [hseg_len, ← hwlen]
            omega
          exact ih seg.length hseg_lt seg rfl hseg_odd
        · have hseg_even : Even seg.length := Nat.not_odd_iff_even.mp hseg_odd
          have hcomp_odd : Odd comp.length := by
            by_contra hcomp_not_odd
            have hcomp_even : Even comp.length := Nat.not_odd_iff_even.mp hcomp_not_odd
            have hsum_even : Even (seg.length + comp.length) := hseg_even.add hcomp_even
            have hsum_odd : Odd (seg.length + comp.length) := hsum ▸ hodd
            exact (Nat.not_odd_iff_even.mpr hsum_even) hsum_odd
          have hcomp_lt : comp.length < n := by
            rw [hcomp_len, ← hwlen]
            omega
          exact ih comp.length hcomp_lt comp rfl hcomp_odd)
  intro a w hodd
  exact aux w.length w rfl hodd

/--
Diestel, Proposition 1.6.1.
A graph is bipartite iff it contains no odd cycle.
-/
theorem proposition_1_6_1 {V : Type u} (G : SimpleGraph V) :
    G.IsBipartite ↔ ∀ a : V, ∀ c : G.Walk a a, c.IsCycle → ¬ Odd c.length := by
  constructor
  · intro hb a c _ hodd
    have heven : Even c.length := SimpleGraph.two_colorable_iff_forall_loop_even.mp hb a c
    exact (Nat.not_odd_iff_even.mpr heven) hodd
  · intro hno
    exact SimpleGraph.two_colorable_iff_forall_loop_even.mpr (by
      intro a w
      by_contra hnot_even
      have hodd : Odd w.length := Nat.not_even_iff_odd.mp hnot_even
      obtain ⟨b, c, hc, hcodd⟩ := odd_closed_walk_contains_odd_cycle w hodd
      exact hno b c hc hcodd)

end Chapter01
end Diestel
