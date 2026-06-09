import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private abbrev Layer {V : Type u} (G : SimpleGraph V) (z : V) (i : ℕ) :=
  {v : V // G.dist z v = i}

private lemma exists_previous_layer
    {V : Type u} {G : SimpleGraph V} (hconn : G.Connected) {z v : V} {i : ℕ}
    (hi : 0 < i) (hv : G.dist z v = i) :
    ∃ u : V, G.Adj u v ∧ G.dist z u = i - 1 := by
  classical
  obtain ⟨p, _hp_path, hp_len⟩ := hconn.exists_path_of_dist z v
  refine ⟨p.getVert (i - 1), ?_, ?_⟩
  · have hlt : i - 1 < p.length := by
      rw [hp_len, hv]
      omega
    have hadj := p.adj_getVert_succ hlt
    have hsucc : (i - 1) + 1 = i := by omega
    have hvlast : p.getVert i = v := by
      rw [← hv, ← hp_len, SimpleGraph.Walk.getVert_length]
    simpa [hsucc, hvlast] using hadj
  · have hsub :
        (p.take (i - 1)).length = G.dist z (p.getVert (i - 1)) := by
      exact SimpleGraph.length_eq_dist_of_subwalk hp_len (SimpleGraph.Walk.isSubwalk_take p (i - 1))
    have htake : (p.take (i - 1)).length = i - 1 := by
      rw [SimpleGraph.Walk.take_length, hp_len, hv]
      omega
    exact hsub.symm.trans htake

private lemma layer_zero_card
    {V : Type u} {G : SimpleGraph V} [Fintype V] (hconn : G.Connected) (z : V) :
    Fintype.card (Layer G z 0) = 1 := by
  classical
  refine Fintype.card_eq_one_of_forall_eq (i := (⟨z, by simp⟩ : Layer G z 0)) ?_
  intro x
  apply Subtype.ext
  exact ((hconn.dist_eq_zero_iff).mp x.property).symm

private lemma layer_one_card_le
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (z : V) {d : ℕ} (hΔ : G.maxDegree ≤ d) :
    Fintype.card (Layer G z 1) ≤ d := by
  classical
  let f : Layer G z 1 → G.neighborSet z :=
    fun v => ⟨v.1, by
      rw [SimpleGraph.mem_neighborSet]
      exact SimpleGraph.dist_eq_one_iff_adj.mp v.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun w : G.neighborSet z => (w : V)) hxy
  calc
    Fintype.card (Layer G z 1) ≤ Fintype.card (G.neighborSet z) :=
      Fintype.card_le_of_injective f hf
    _ = G.degree z := SimpleGraph.card_neighborSet_eq_degree G z
    _ ≤ G.maxDegree := G.degree_le_maxDegree z
    _ ≤ d := hΔ

private lemma choice_card_le
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    {u p : V} (hpu : G.Adj p u) {d : ℕ} (hΔ : G.maxDegree ≤ d) :
    Nat.card {w : V // G.Adj u w ∧ w ≠ p} ≤ d - 1 := by
  classical
  letI : Finite {w : V // G.Adj u w ∧ w ≠ p} :=
    Finite.of_injective (fun w : {w : V // G.Adj u w ∧ w ≠ p} => (w : V))
      (fun _ _ h => Subtype.ext h)
  letI : Fintype {w : V // G.Adj u w ∧ w ≠ p} :=
    Fintype.ofFinite _
  let f : {w : V // G.Adj u w ∧ w ≠ p} → G.neighborSet u :=
    fun w => ⟨w.1, by
      rw [SimpleGraph.mem_neighborSet]
      exact w.2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun w : G.neighborSet u => (w : V)) hxy
  have hnot :
      (⟨p, by
        rw [SimpleGraph.mem_neighborSet]
        exact hpu.symm⟩ : G.neighborSet u) ∉ Set.range f := by
    rintro ⟨w, hw⟩
    have hpw : w.1 = p := congrArg Subtype.val hw
    exact w.2.2 hpw
  have hlt :
      Fintype.card {w : V // G.Adj u w ∧ w ≠ p} < Fintype.card (G.neighborSet u) :=
    Fintype.card_lt_of_injective_of_notMem f hf hnot
  have hdeg : Fintype.card (G.neighborSet u) = G.degree u :=
    SimpleGraph.card_neighborSet_eq_degree G u
  have hdeg_le : G.degree u ≤ d := (G.degree_le_maxDegree u).trans hΔ
  rw [Nat.card_eq_fintype_card]
  omega

private lemma layer_succ_succ_card_le
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (z : V) {d : ℕ} (hΔ : G.maxDegree ≤ d) (i : ℕ) :
    Fintype.card (Layer G z (i + 2)) ≤
      (d - 1) * Fintype.card (Layer G z (i + 1)) := by
  classical
  let parent : Layer G z (i + 2) → Layer G z (i + 1) :=
    fun x =>
      let h := exists_previous_layer hconn (z := z) (v := x.1)
        (by omega : 0 < i + 2) x.2
      ⟨Classical.choose h, by
        have hs := (Classical.choose_spec h).2
        simpa using hs⟩
  let parent_adj : ∀ x : Layer G z (i + 2), G.Adj (parent x).1 x.1 := by
    intro x
    dsimp [parent]
    exact (Classical.choose_spec
      (exists_previous_layer hconn (z := z) (v := x.1) (by omega : 0 < i + 2) x.2)).1
  let prev : Layer G z (i + 1) → V :=
    fun y =>
      let h := exists_previous_layer hconn (z := z) (v := y.1)
        (by omega : 0 < i + 1) y.2
      Classical.choose h
  have prev_adj : ∀ y : Layer G z (i + 1), G.Adj (prev y) y.1 := by
    intro y
    dsimp [prev]
    exact (Classical.choose_spec
      (exists_previous_layer hconn (z := z) (v := y.1) (by omega : 0 < i + 1) y.2)).1
  have prev_dist : ∀ y : Layer G z (i + 1), G.dist z (prev y) = i := by
    intro y
    dsimp [prev]
    exact (Classical.choose_spec
      (exists_previous_layer hconn (z := z) (v := y.1) (by omega : 0 < i + 1) y.2)).2
  let Choice (y : Layer G z (i + 1)) := {w : V // G.Adj y.1 w ∧ w ≠ prev y}
  letI : ∀ y : Layer G z (i + 1), Finite (Choice y) := by
    intro y
    exact Finite.of_injective (fun w : Choice y => (w : V)) (fun _ _ h => Subtype.ext h)
  letI : ∀ y : Layer G z (i + 1), Fintype (Choice y) := by
    intro y
    exact Fintype.ofFinite (Choice y)
  let emb : Layer G z (i + 2) ↪ Sigma Choice :=
    { toFun := fun x =>
        ⟨parent x, ⟨x.1, by
          refine ⟨parent_adj x, ?_⟩
          intro hx
          have hchild : G.dist z x.1 = i + 2 := x.2
          have hprev : G.dist z (prev (parent x)) = i := prev_dist (parent x)
          rw [hx] at hchild
          omega⟩⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun s : Sigma Choice => (s.2 : V)) hxy }
  calc
    Fintype.card (Layer G z (i + 2)) ≤ Fintype.card (Sigma Choice) :=
      Fintype.card_le_of_embedding emb
    _ = ∑ y : Layer G z (i + 1), Fintype.card (Choice y) := Fintype.card_sigma
    _ ≤ ∑ _y : Layer G z (i + 1), (d - 1) := by
      refine Finset.sum_le_sum fun y _hy => ?_
      have h := choice_card_le G (prev_adj y) hΔ
      simpa [Nat.card_eq_fintype_card] using h
    _ = Fintype.card (Layer G z (i + 1)) * (d - 1) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (d - 1) * Fintype.card (Layer G z (i + 1)) := by
      rw [Nat.mul_comm]

private lemma layer_positive_card_le
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (z : V) {d : ℕ} (hΔ : G.maxDegree ≤ d) :
    ∀ j : ℕ, Fintype.card (Layer G z (j + 1)) ≤ d * (d - 1) ^ j
  | 0 => by
      simpa using layer_one_card_le G z hΔ
  | j + 1 => by
      have hrec := layer_positive_card_le G hconn z hΔ j
      have hstep := layer_succ_succ_card_le G hconn z hΔ j
      calc
        Fintype.card (Layer G z (j + 1 + 1)) ≤
            (d - 1) * Fintype.card (Layer G z (j + 1)) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
        _ ≤ (d - 1) * (d * (d - 1) ^ j) := by
          exact Nat.mul_le_mul_left (d - 1) hrec
        _ = d * (d - 1) ^ (j + 1) := by
          ring

private lemma card_le_radius_layers
    {V : Type u} {G : SimpleGraph V} [Fintype V] (hconn : G.Connected)
    {z : V} {k : ℕ} (hdist : ∀ v : V, G.dist z v ≤ k) :
    Fintype.card V ≤
      1 + Fintype.card (Sigma fun j : Fin k => Layer G z (j.1 + 1)) := by
  classical
  let f : V → Option (Sigma fun j : Fin k => Layer G z (j.1 + 1)) :=
    fun v =>
      if h0 : G.dist z v = 0 then
        none
      else
        some ⟨⟨G.dist z v - 1, by
          have hvle := hdist v
          have hvpos : 0 < G.dist z v := Nat.pos_of_ne_zero h0
          change G.dist z v - 1 < k
          omega⟩, ⟨v, by
            have hvpos : 0 < G.dist z v := Nat.pos_of_ne_zero h0
            change G.dist z v = (G.dist z v - 1) + 1
            omega⟩⟩
  have hf : Function.Injective f := by
    intro v w hvw
    by_cases hv0 : G.dist z v = 0 <;> by_cases hw0 : G.dist z w = 0
    · have hvz : z = v := (hconn.dist_eq_zero_iff).mp hv0
      have hwz : z = w := (hconn.dist_eq_zero_iff).mp hw0
      exact hvz.symm.trans hwz
    · have hvf : f v = none := by
        dsimp [f]
        rw [dif_pos hv0]
      have hwf : f w ≠ none := by
        dsimp [f]
        rw [dif_neg hw0]
        exact Option.some_ne_none _
      rw [hvf] at hvw
      exact False.elim (hwf hvw.symm)
    · have hvf : f v ≠ none := by
        dsimp [f]
        rw [dif_neg hv0]
        exact Option.some_ne_none _
      have hwf : f w = none := by
        dsimp [f]
        rw [dif_pos hw0]
      rw [hwf] at hvw
      exact False.elim (hvf hvw)
    · let sv : Sigma fun j : Fin k => Layer G z (j.1 + 1) :=
        ⟨⟨G.dist z v - 1, by
            have hvle := hdist v
            have hvpos : 0 < G.dist z v := Nat.pos_of_ne_zero hv0
            change G.dist z v - 1 < k
            omega⟩, ⟨v, by
              have hvpos : 0 < G.dist z v := Nat.pos_of_ne_zero hv0
              change G.dist z v = (G.dist z v - 1) + 1
              omega⟩⟩
      let sw : Sigma fun j : Fin k => Layer G z (j.1 + 1) :=
        ⟨⟨G.dist z w - 1, by
            have hwle := hdist w
            have hwpos : 0 < G.dist z w := Nat.pos_of_ne_zero hw0
            change G.dist z w - 1 < k
            omega⟩, ⟨w, by
              have hwpos : 0 < G.dist z w := Nat.pos_of_ne_zero hw0
              change G.dist z w = (G.dist z w - 1) + 1
              omega⟩⟩
      have hvf : f v = some sv := by
        dsimp [f, sv]
        rw [dif_neg hv0]
      have hwf : f w = some sw := by
        dsimp [f, sw]
        rw [dif_neg hw0]
      have hsome : sv = sw := by
        rw [hvf, hwf] at hvw
        exact Option.some.inj hvw
      exact congrArg (fun s : Sigma fun j : Fin k => Layer G z (j.1 + 1) => (s.2 : V)) hsome
  calc
    Fintype.card V ≤ Fintype.card (Option (Sigma fun j : Fin k => Layer G z (j.1 + 1))) :=
      Fintype.card_le_of_injective f hf
    _ = 1 + Fintype.card (Sigma fun j : Fin k => Layer G z (j.1 + 1)) := by
      rw [Fintype.card_option]
      omega

private lemma finite_geometric_bound (k d : ℕ) (hd : 3 ≤ d) :
    (1 + ∑ j : Fin k, d * (d - 1) ^ (j : ℕ) : ℚ) <
      ((d : ℚ) / ((d : ℚ) - 2)) * ((d : ℚ) - 1) ^ k := by
  classical
  have hdq2 : (2 : ℚ) < d := by
    have hd' : 2 < d := by omega
    exact_mod_cast hd'
  have hbase_gt_one : (1 : ℚ) < (d : ℚ) - 1 := by linarith
  have hden_ne : (d : ℚ) - 2 ≠ 0 := by linarith
  have hbase_ne_one : (d : ℚ) - 1 ≠ 1 := by linarith
  rw [Nat.cast_sum]
  have hsum_cast :
      (∑ x : Fin k, ((d * (d - 1) ^ (x : ℕ) : ℕ) : ℚ)) =
        ∑ x : Fin k, (d : ℚ) * ((d : ℚ) - 1) ^ (x : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [Nat.cast_mul, Nat.cast_pow]
    have hd1 : 1 ≤ d := by omega
    rw [Nat.cast_sub hd1, Nat.cast_one]
  rw [hsum_cast]
  have hfin :
      (∑ x : Fin k, (d : ℚ) * ((d : ℚ) - 1) ^ (x : ℕ)) =
        ∑ j ∈ Finset.range k, (d : ℚ) * ((d : ℚ) - 1) ^ j :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => (d : ℚ) * ((d : ℚ) - 1) ^ j) k
  rw [hfin]
  have hgeom :
      ∑ j ∈ Finset.range k, (d : ℚ) * ((d : ℚ) - 1) ^ j =
        (d : ℚ) * (((d : ℚ) - 1) ^ k - 1) / ((d : ℚ) - 2) := by
    rw [← Finset.mul_sum, geom_sum_eq hbase_ne_one]
    ring_nf
  rw [hgeom]
  have hden_pos : 0 < (d : ℚ) - 2 := by linarith
  rw [div_mul_eq_mul_div]
  rw [lt_div_iff₀ hden_pos]
  field_simp [hden_ne]
  ring_nf
  linarith

/--
Diestel, Proposition 1.3.3.
A graph of radius at most `k` and maximum degree at most `d ≥ 3` has
fewer than `d / (d - 2) * (d - 1)^k` vertices.
-/
theorem proposition_1_3_3 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [Nonempty V] [DecidableRel G.Adj] (k d : ℕ) :
  G.radius ≤ (k : ℕ∞) →
    G.maxDegree ≤ d →
      3 ≤ d →
        (Fintype.card V : ℚ) <
          ((d : ℚ) / ((d : ℚ) - 2)) * ((d : ℚ) - 1) ^ k := by
  classical
  intro hrad hΔ hd
  obtain ⟨z, hz⟩ := G.exists_eccent_eq_radius
  have hecc : G.eccent z ≤ (k : ℕ∞) := by
    rw [hz]
    exact hrad
  have hconn : G.Connected := by
    rw [← SimpleGraph.radius_ne_top_iff]
    exact ne_top_of_le_ne_top (by exact ENat.coe_ne_top k) hrad
  have hdist : ∀ v : V, G.dist z v ≤ k := by
    intro v
    have hed : G.edist z v ≤ (k : ℕ∞) := (SimpleGraph.eccent_le_iff z (k : ℕ∞)).mp hecc v
    have hreach : G.Reachable z v := hconn z v
    have hcoe : (G.dist z v : ℕ∞) = G.edist z v := hreach.coe_dist_eq_edist
    exact ENat.coe_le_coe.mp (by simpa [hcoe] using hed)
  have hcard_layers := card_le_radius_layers hconn hdist
  have hsum_layers :
      Fintype.card (Sigma fun j : Fin k => Layer G z (j.1 + 1)) ≤
        ∑ j : Fin k, d * (d - 1) ^ (j : ℕ) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_le_sum fun j _hj => layer_positive_card_le G hconn z hΔ j.1
  have hnat :
      Fintype.card V ≤ 1 + ∑ j : Fin k, d * (d - 1) ^ (j : ℕ) := by
    exact hcard_layers.trans (Nat.add_le_add_left hsum_layers 1)
  have hlt := finite_geometric_bound k d hd
  exact lt_of_le_of_lt (by exact_mod_cast hnat) hlt

end Chapter01
end Diestel
