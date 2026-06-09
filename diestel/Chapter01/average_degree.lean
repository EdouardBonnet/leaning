import Chapter01.definitions_ch1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

theorem average_degree_eq_two_mul_edge_vertex_ratio {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    average_degree G = 2 * edge_vertex_ratio G := by
  rw [average_degree, edge_vertex_ratio]
  rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
  change ((2 * G.edgeFinset.card : ℕ) : ℚ) / (Fintype.card V : ℚ) =
    2 * ((G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ))
  rw [Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem average_degree_nonneg {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    0 ≤ average_degree G := by
  rw [average_degree]
  exact div_nonneg
    (Finset.sum_nonneg fun _ _ => by exact_mod_cast Nat.zero_le _)
    (by exact_mod_cast Nat.zero_le (Fintype.card V))

theorem edge_vertex_ratio_nonneg {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    0 ≤ edge_vertex_ratio G := by
  rw [edge_vertex_ratio]
  exact div_nonneg
    (by exact_mod_cast Nat.zero_le G.edgeFinset.card)
    (by exact_mod_cast Nat.zero_le (Fintype.card V))

theorem nonempty_of_average_degree_pos {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    0 < average_degree G → Nonempty V := by
  intro h
  by_contra hne
  haveI : IsEmpty V := not_nonempty_iff.mp hne
  simp [average_degree] at h

theorem average_degree_lt_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] [Nonempty V] :
    average_degree G < (Fintype.card V : ℚ) := by
  rw [average_degree]
  have hsum_lt : (∑ v : V, (G.degree v : ℚ)) < ∑ v : V, (Fintype.card V : ℚ) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro v _
      exact_mod_cast SimpleGraph.degree_lt_card_verts (G := G) v
  have hcard_pos : (0 : ℚ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  calc
    (∑ v : V, (G.degree v : ℚ)) / (Fintype.card V : ℚ)
        < (∑ v : V, (Fintype.card V : ℚ)) / (Fintype.card V : ℚ) := by
          exact div_lt_div_of_pos_right hsum_lt hcard_pos
    _ = (Fintype.card V : ℚ) := by
          simp

theorem lt_card_of_lt_average_degree {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {a : ℚ} :
    a < average_degree G → 0 ≤ a → a < (Fintype.card V : ℚ) := by
  intro h ha
  have hpos : 0 < average_degree G := lt_of_le_of_lt ha h
  haveI : Nonempty V := nonempty_of_average_degree_pos G hpos
  exact lt_trans h (average_degree_lt_card G)

end Chapter01
end Diestel
