import Chapter01.average_degree
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

open scoped BigOperators

/--
The dense induced subgraphs used in Diestel's proof of Mader's theorem.
Here `ε(G)` is `edge_vertex_ratio G`, so the density condition is
`‖G[U]‖ > ε(G) (|U| - k)`.
-/
noncomputable def mader_candidate {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (k : ℕ) (U : Set V) : Prop :=
  2 * k ≤ U.ncard ∧
    edge_vertex_ratio G * ((U.ncard : ℚ) - (k : ℚ)) <
      (Nat.card (G.induce U).edgeSet : ℚ)

def mader_liftSet {V : Type u} (S : Set V) (B : Set S) : Set V :=
  Subtype.val '' B

private noncomputable def induce_mader_liftSet_iso {V : Type u} (G : SimpleGraph V)
    (S : Set V) (B : Set S) :
    G.induce (mader_liftSet S B) ≃g (G.induce S).induce B where
  toEquiv := (Equiv.Set.image (fun x : S => (x : V)) B Subtype.val_injective).symm
  map_rel_iff' := by
    intro x y
    rcases x with ⟨_, ⟨x, hxB, rfl⟩⟩
    rcases y with ⟨_, ⟨y, hyB, rfl⟩⟩
    let e := Equiv.Set.image (fun x : S => (x : V)) B Subtype.val_injective
    have hx :
        e.symm ⟨(x : V), by exact ⟨x, hxB, rfl⟩⟩ = ⟨x, hxB⟩ :=
      Equiv.Set.image_symm_apply (fun x : S => (x : V)) B Subtype.val_injective x _
    have hy :
        e.symm ⟨(y : V), by exact ⟨y, hyB, rfl⟩⟩ = ⟨y, hyB⟩ :=
      Equiv.Set.image_symm_apply (fun x : S => (x : V)) B Subtype.val_injective y _
    change G.Adj (((e.symm ⟨(x : V), by exact ⟨x, hxB, rfl⟩⟩ : B) : S) : V)
        (((e.symm ⟨(y : V), by exact ⟨y, hyB, rfl⟩⟩ : B) : S) : V) ↔
      G.Adj (x : V) (y : V)
    rw [hx, hy]

private noncomputable def sym2Restrict {V : Type u} (S : Set V)
    (e : Sym2 V) (hS : ∀ v : V, v ∈ e → v ∈ S) : Sym2 S :=
  let p := Quot.out e
  s(⟨p.1, hS p.1 (by
      have hout : s(p.1, p.2) = e := Quot.out_eq e
      rw [← hout]
      exact Sym2.mem_iff.mpr (Or.inl rfl))⟩,
    ⟨p.2, hS p.2 (by
      have hout : s(p.1, p.2) = e := Quot.out_eq e
      rw [← hout]
      exact Sym2.mem_iff.mpr (Or.inr rfl))⟩)

private theorem sym2_map_val_restrict {V : Type u} (S : Set V)
    (e : Sym2 V) (hS : ∀ v : V, v ∈ e → v ∈ S) :
    Sym2.map (fun x : S => (x : V)) (sym2Restrict S e hS) = e := by
  unfold sym2Restrict
  let p := Quot.out e
  have hout : s(p.1, p.2) = e := Quot.out_eq e
  rw [Sym2.map_mk]
  exact hout

private theorem sym2Restrict_mem_induce_edgeSet {V : Type u} (H : SimpleGraph V)
    (S : Set V) (e : H.edgeSet) (hS : ∀ v : V, v ∈ (e : Sym2 V) → v ∈ S) :
    sym2Restrict S (e : Sym2 V) hS ∈ (H.induce S).edgeSet := by
  unfold sym2Restrict
  let p := Quot.out (e : Sym2 V)
  rw [SimpleGraph.mem_edgeSet]
  change H.Adj p.1 p.2
  have hout : s(p.1, p.2) = (e : Sym2 V) := Quot.out_eq (e : Sym2 V)
  have he : s(p.1, p.2) ∈ H.edgeSet := by
    rw [hout]
    exact e.2
  exact (SimpleGraph.mem_edgeSet H).mp he

private def edgeSetInside {V : Type u} (H : SimpleGraph V) (S : Set V) : Set H.edgeSet :=
  {e | ∀ v : V, v ∈ (e : Sym2 V) → v ∈ S}

private def induce_diff_singleton_iso {V : Type u} (G : SimpleGraph V)
    (U : Set V) (v : U) :
    G.induce (U \ {v.1}) ≃g (G.induce U).induce ({v}ᶜ : Set U) where
  toFun x := ⟨⟨x.1, x.2.1⟩, by
    intro h
    exact x.2.2 (by
      rw [Set.mem_singleton_iff]
      exact congrArg Subtype.val h)⟩
  invFun x := ⟨x.1.1, x.1.2, by
    intro h
    exact x.2 (by
      rw [Set.mem_singleton_iff]
      exact Subtype.ext (Set.mem_singleton_iff.mp h))⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

theorem edgeSet_nat_card_induce_univ {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    Nat.card (G.induce (Set.univ : Set V)).edgeSet = Nat.card G.edgeSet := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
  exact (SimpleGraph.induceUnivIso G).card_edgeFinset_eq

theorem edgeSet_nat_card_eq_edgeFinset_card {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

theorem mader_liftSet_ncard {V : Type u} (S : Set V) (B : Set S) :
    (mader_liftSet S B).ncard = B.ncard := by
  exact Set.ncard_image_of_injective B Subtype.val_injective

theorem edgeSet_nat_card_induce_mader_liftSet {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (S : Set V) (B : Set S) :
    Nat.card (G.induce (mader_liftSet S B)).edgeSet =
      Nat.card ((G.induce S).induce B).edgeSet := by
  classical
  letI : Fintype (mader_liftSet S B) := Fintype.ofFinite (mader_liftSet S B)
  letI : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
  exact (induce_mader_liftSet_iso G S B).card_edgeFinset_eq

private theorem edgeSetInside_ncard_le {V : Type u} (H : SimpleGraph V) [Fintype V]
    (S : Set V) :
    (edgeSetInside H S).ncard ≤ Nat.card (H.induce S).edgeSet := by
  classical
  let f : edgeSetInside H S → (H.induce S).edgeSet := fun e =>
    ⟨sym2Restrict S (e.1 : Sym2 V) e.2,
      sym2Restrict_mem_induce_edgeSet H S e.1 e.2⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ heq
    apply Subtype.ext
    apply Subtype.ext
    have hmap := congrArg (fun z : (H.induce S).edgeSet =>
      Sym2.map (fun x : S => (x : V)) (z : Sym2 S)) heq
    change Sym2.map (fun x : S => (x : V)) (sym2Restrict S (e₁.1 : Sym2 V) e₁.2) =
      Sym2.map (fun x : S => (x : V)) (sym2Restrict S (e₂.1 : Sym2 V) e₂.2) at hmap
    rw [sym2_map_val_restrict, sym2_map_val_restrict] at hmap
    exact hmap
  have hcard := Nat.card_le_card_of_injective f hf
  have hleft : Nat.card (edgeSetInside H S) = (edgeSetInside H S).ncard :=
    Nat.card_coe_set_eq (edgeSetInside H S)
  rw [hleft] at hcard
  exact hcard

private theorem edgeSetInside_cover_of_separation {V : Type u} (H : SimpleGraph V)
    {A B : Set V} (hsep : IsSeparation H A B) :
    edgeSetInside H A ∪ edgeSetInside H B = Set.univ := by
  have hcover_edge : ∀ z : Sym2 V, ∀ hz : z ∈ H.edgeSet,
      (⟨z, hz⟩ : H.edgeSet) ∈ edgeSetInside H A ∨
        (⟨z, hz⟩ : H.edgeSet) ∈ edgeSetInside H B := by
    intro z hz
    induction z using Sym2.inductionOn with
    | hf x y =>
        have hxy : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp hz
        have hx_union : x ∈ A ∪ B := by
          have : x ∈ Set.univ := Set.mem_univ x
          rw [← hsep.1] at this
          exact this
        have hy_union : y ∈ A ∪ B := by
          have : y ∈ Set.univ := Set.mem_univ y
          rw [← hsep.1] at this
          exact this
        rcases hx_union with hxA | hxB
        · by_cases hyA : y ∈ A
          · exact Or.inl (by
              change ∀ v : V, v ∈ s(x, y) → v ∈ A
              intro v hv
              rcases Sym2.mem_iff.mp hv with hvx | hvy
              · exact hvx.symm ▸ hxA
              · exact hvy.symm ▸ hyA)
          · have hyB : y ∈ B := by
              rcases hy_union with hyA' | hyB
              · exact False.elim (hyA hyA')
              · exact hyB
            have hxB : x ∈ B := by
              by_contra hxnotB
              exact hsep.2 hxA hxnotB hyB hyA hxy
            exact Or.inr (by
              change ∀ v : V, v ∈ s(x, y) → v ∈ B
              intro v hv
              rcases Sym2.mem_iff.mp hv with hvx | hvy
              · exact hvx.symm ▸ hxB
              · exact hvy.symm ▸ hyB)
        · by_cases hyB : y ∈ B
          · exact Or.inr (by
              change ∀ v : V, v ∈ s(x, y) → v ∈ B
              intro v hv
              rcases Sym2.mem_iff.mp hv with hvx | hvy
              · exact hvx.symm ▸ hxB
              · exact hvy.symm ▸ hyB)
          · have hyA : y ∈ A := by
              rcases hy_union with hyA | hyB'
              · exact hyA
              · exact False.elim (hyB hyB')
            have hxA : x ∈ A := by
              by_contra hxnotA
              exact hsep.2 hyA hyB hxB hxnotA hxy.symm
            exact Or.inl (by
              change ∀ v : V, v ∈ s(x, y) → v ∈ A
              intro v hv
              rcases Sym2.mem_iff.mp hv with hvx | hvy
              · exact hvx.symm ▸ hxA
              · exact hvy.symm ▸ hyA)
  ext e
  constructor
  · intro _
    exact Set.mem_univ e
  · intro _
    exact hcover_edge e.1 e.2

theorem edgeSet_nat_card_le_separation_sides {V : Type u} (H : SimpleGraph V)
    [Fintype V] {A B : Set V} (hsep : IsSeparation H A B) :
    Nat.card H.edgeSet ≤
      Nat.card (H.induce A).edgeSet + Nat.card (H.induce B).edgeSet := by
  classical
  have hcover := edgeSetInside_cover_of_separation H hsep
  have hcard_cover : Nat.card H.edgeSet ≤
      (edgeSetInside H A).ncard + (edgeSetInside H B).ncard := by
    rw [← Set.ncard_univ (H.edgeSet), ← hcover]
    exact Set.ncard_union_le (edgeSetInside H A) (edgeSetInside H B)
  have hA := edgeSetInside_ncard_le H A
  have hB := edgeSetInside_ncard_le H B
  omega

theorem edgeSet_nat_card_induce_diff_singleton {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {U : Set V}
    [Fintype U] [DecidableRel (G.induce U).Adj] (v : U) :
    Nat.card (G.induce (U \ {v.1})).edgeSet =
      Nat.card (G.induce U).edgeSet - (G.induce U).degree v := by
  classical
  letI : DecidableEq V := Classical.decEq V
  let H : SimpleGraph U := G.induce U
  let W : Set V := U \ {v.1}
  have hH_edges :
      Nat.card (G.induce W).edgeSet =
        Nat.card H.edgeSet - H.degree v := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
    calc
      (G.induce W).edgeFinset.card =
          ((H.induce ({v}ᶜ : Set U)).edgeFinset.card) := by
        rw [(induce_diff_singleton_iso G U v).card_edgeFinset_eq]
      _ = (H.deleteIncidenceSet v).edgeFinset.card := by
        rw [SimpleGraph.card_edgeFinset_induce_compl_singleton]
      _ = H.edgeFinset.card - H.degree v := by
        rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  exact hH_edges

theorem edgeSet_nat_card_le_half_mul_pred {V : Type u} (H : SimpleGraph V)
    [Fintype V] [DecidableRel H.Adj] :
    (Nat.card H.edgeSet : ℚ) ≤
      (Fintype.card V : ℚ) * ((Fintype.card V : ℚ) - 1) / 2 := by
  have hdeg_le : ∀ v : V, (H.degree v : ℚ) ≤ (Fintype.card V : ℚ) - 1 := by
    intro v
    have hlt : H.degree v < Fintype.card V := SimpleGraph.degree_lt_card_verts (G := H) v
    have hle_nat : H.degree v ≤ Fintype.card V - 1 := by omega
    have hcard_one : 1 ≤ Fintype.card V := by omega
    have hcast : ((Fintype.card V - 1 : ℕ) : ℚ) = (Fintype.card V : ℚ) - 1 := by
      rw [Nat.cast_sub hcard_one]
      norm_num
    rw [← hcast]
    exact_mod_cast hle_nat
  have hsum_le : (∑ v : V, (H.degree v : ℚ)) ≤
      ∑ v : V, ((Fintype.card V : ℚ) - 1) := by
    exact Finset.sum_le_sum fun v _ => hdeg_le v
  have hsum_eq : (∑ v : V, (H.degree v : ℚ)) = (2 * H.edgeFinset.card : ℚ) := by
    rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [Nat.cast_mul, Nat.cast_ofNat]
  have htwo_edges_le : (2 * H.edgeFinset.card : ℚ) ≤
      (Fintype.card V : ℚ) * ((Fintype.card V : ℚ) - 1) := by
    calc
      (2 * H.edgeFinset.card : ℚ) = ∑ v : V, (H.degree v : ℚ) := hsum_eq.symm
      _ ≤ ∑ v : V, ((Fintype.card V : ℚ) - 1) := hsum_le
      _ = (Fintype.card V : ℚ) * ((Fintype.card V : ℚ) - 1) := by
        simp
        ring
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  nlinarith

theorem mader_candidate_univ {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) :
    mader_candidate G k Set.univ := by
  have h4_nonneg : 0 ≤ (4 * k : ℚ) := by positivity
  have h4_lt_card : (4 * k : ℚ) < (Fintype.card V : ℚ) :=
    lt_card_of_lt_average_degree G havg h4_nonneg
  have h2_lt_card : (2 * k : ℚ) < (Fintype.card V : ℚ) := by
    nlinarith
  have horder : 2 * k ≤ (Set.univ : Set V).ncard := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    exact Nat.le_of_lt (by exact_mod_cast h2_lt_card)
  refine ⟨horder, ?_⟩
  have h_avg_pos : 0 < average_degree G := by nlinarith
  haveI : Nonempty V := nonempty_of_average_degree_pos G h_avg_pos
  have hn_pos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hk_pos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have h_eps_eq : edge_vertex_ratio G = average_degree G / 2 := by
    rw [average_degree_eq_two_mul_edge_vertex_ratio G]
    ring
  have h_eps_pos : 0 < edge_vertex_ratio G := by
    rw [h_eps_eq]
    positivity
  have h_edges_as_ratio :
      (G.edgeFinset.card : ℚ) = edge_vertex_ratio G * (Fintype.card V : ℚ) := by
    rw [edge_vertex_ratio]
    field_simp [hn_pos.ne']
  rw [edgeSet_nat_card_induce_univ]
  rw [edgeSet_nat_card_eq_edgeFinset_card]
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  change edge_vertex_ratio G * ((Fintype.card V : ℚ) - (k : ℚ)) <
    (G.edgeFinset.card : ℚ)
  rw [h_edges_as_ratio]
  nlinarith [mul_pos h_eps_pos hk_pos]

theorem exists_minimal_mader_candidate {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) :
    ∃ U : Set V, MinimalFor (fun W => mader_candidate G k W) Set.ncard U := by
  let candidates : Set (Set V) := {U | mader_candidate G k U}
  have hfinite : candidates.Finite := Set.toFinite candidates
  have hnonempty : candidates.Nonempty := ⟨Set.univ, mader_candidate_univ G hk havg⟩
  exact hfinite.exists_minimalFor Set.ncard candidates hnonempty

theorem mader_candidate_ncard_ne_two_mul {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) {U : Set V}
    (hU : mader_candidate G k U) :
    U.ncard ≠ 2 * k := by
  intro hcard
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : DecidableRel (G.induce U).Adj := Classical.decRel (G.induce U).Adj
  have h_eps_gt : (2 * k : ℚ) < edge_vertex_ratio G := by
    have htmp : (4 * k : ℚ) < 2 * edge_vertex_ratio G := by
      rwa [average_degree_eq_two_mul_edge_vertex_ratio G] at havg
    nlinarith
  have hk_pos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hdense : edge_vertex_ratio G * (k : ℚ) <
      (Nat.card (G.induce U).edgeSet : ℚ) := by
    have := hU.2
    rw [hcard] at this
    rw [Nat.cast_mul, Nat.cast_ofNat] at this
    ring_nf at this
    exact this
  have hUcard_fintype : Fintype.card U = U.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq U
  have hbound := edgeSet_nat_card_le_half_mul_pred (G.induce U)
  rw [hUcard_fintype, hcard] at hbound
  rw [Nat.cast_mul, Nat.cast_ofNat] at hbound
  ring_nf at hbound
  have h_eps_k : (2 * k : ℚ) * (k : ℚ) < edge_vertex_ratio G * (k : ℚ) :=
    mul_lt_mul_of_pos_right h_eps_gt hk_pos
  nlinarith [h_eps_k, hbound, hdense]

theorem mader_candidate_diff_singleton_of_degree_le {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} {U : Set V}
    [Fintype U] [DecidableRel (G.induce U).Adj]
    (hU : mader_candidate G k U) (hne : U.ncard ≠ 2 * k) (v : U)
    (hdeg : ((G.induce U).degree v : ℚ) ≤ edge_vertex_ratio G) :
    mader_candidate G k (U \ {v.1}) := by
  classical
  let W : Set V := U \ {v.1}
  have hcardW_add : W.ncard + 1 = U.ncard := by
    exact Set.ncard_diff_singleton_add_one (s := U) (a := v.1) v.2
  have horderU_strict : 2 * k < U.ncard := by
    exact lt_of_le_of_ne hU.1 (fun h => hne h.symm)
  have horderW : 2 * k ≤ W.ncard := by omega
  refine ⟨horderW, ?_⟩
  have h_edges_eq := edgeSet_nat_card_induce_diff_singleton G v
  have hdeg_le_edges : (G.induce U).degree v ≤ Nat.card (G.induce U).edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact (G.induce U).degree_le_card_edgeFinset v
  have h_edges_cast :
      (Nat.card (G.induce W).edgeSet : ℚ) =
        (Nat.card (G.induce U).edgeSet : ℚ) - ((G.induce U).degree v : ℚ) := by
    rw [h_edges_eq]
    rw [Nat.cast_sub hdeg_le_edges]
  have hcardW_add_q : (W.ncard : ℚ) + 1 = (U.ncard : ℚ) := by
    exact_mod_cast hcardW_add
  rw [h_edges_cast]
  nlinarith [hU.2, hdeg, hcardW_add_q]

theorem minimal_mader_candidate_degree_gt {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) {U : Set V}
    [Fintype U] [DecidableRel (G.induce U).Adj]
    (hmin : MinimalFor (fun W => mader_candidate G k W) Set.ncard U) :
    ∀ v : U, edge_vertex_ratio G < ((G.induce U).degree v : ℚ) := by
  intro v
  by_contra hnot
  have hdeg : ((G.induce U).degree v : ℚ) ≤ edge_vertex_ratio G := le_of_not_gt hnot
  have hne : U.ncard ≠ 2 * k := mader_candidate_ncard_ne_two_mul G hk havg hmin.1
  have hW : mader_candidate G k (U \ {v.1}) :=
    mader_candidate_diff_singleton_of_degree_le G hmin.1 hne v hdeg
  have hW_le_U : (U \ {v.1}).ncard ≤ U.ncard :=
    (Set.ncard_diff_singleton_lt_of_mem (s := U) v.2).le
  have hU_le_W := hmin.2 hW hW_le_U
  have hW_lt_U : (U \ {v.1}).ncard < U.ncard :=
    Set.ncard_diff_singleton_lt_of_mem (s := U) v.2
  omega

theorem minimal_mader_candidate_order_gt {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) {U : Set V}
    (hmin : MinimalFor (fun W => mader_candidate G k W) Set.ncard U) :
    k + 1 < Nat.card U := by
  have hne : U.ncard ≠ 2 * k := mader_candidate_ncard_ne_two_mul G hk havg hmin.1
  have hstrict : 2 * k < U.ncard :=
    lt_of_le_of_ne hmin.1.1 (fun h => hne h.symm)
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  rw [Nat.card_coe_set_eq]
  omega

theorem minimal_mader_candidate_edge_vertex_ratio_gt {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) {U : Set V}
    [Fintype U] [DecidableRel (G.induce U).Adj]
    (hmin : MinimalFor (fun W => mader_candidate G k W) Set.ncard U) :
    edge_vertex_ratio G - (k : ℚ) < edge_vertex_ratio (G.induce U) := by
  classical
  have hU : mader_candidate G k U := hmin.1
  have hk_nat_pos : 0 < k := Nat.pos_of_ne_zero hk
  have hk_pos : (0 : ℚ) < k := by exact_mod_cast hk_nat_pos
  have horder : 2 * k ≤ U.ncard := hU.1
  have htwok_pos : 0 < 2 * k := by omega
  have hUpos_nat : 0 < U.ncard := lt_of_lt_of_le htwok_pos horder
  have hUnonempty : U.Nonempty := (Set.ncard_pos (s := U)).mp hUpos_nat
  obtain ⟨x, hxU⟩ := hUnonempty
  let v : U := ⟨x, hxU⟩
  have hdeg_gt := minimal_mader_candidate_degree_gt G hk havg hmin v
  have hdeg_lt_card_nat : (G.induce U).degree v < Fintype.card U :=
    SimpleGraph.degree_lt_card_verts (G := G.induce U) v
  have hUcard_fintype : Fintype.card U = U.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq U
  have h_eps_lt_u : edge_vertex_ratio G < (U.ncard : ℚ) := by
    rw [← hUcard_fintype]
    exact lt_trans hdeg_gt (by exact_mod_cast hdeg_lt_card_nat)
  have hu_pos : (0 : ℚ) < U.ncard := by exact_mod_cast hUpos_nat
  have hE_cast :
      (Nat.card (G.induce U).edgeSet : ℚ) = ((G.induce U).edgeFinset.card : ℚ) := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hdense : edge_vertex_ratio G * ((U.ncard : ℚ) - (k : ℚ)) <
      ((G.induce U).edgeFinset.card : ℚ) := by
    rw [← hE_cast]
    exact hU.2
  have h_eps_k_lt_u_k : edge_vertex_ratio G * (k : ℚ) < (U.ncard : ℚ) * (k : ℚ) :=
    mul_lt_mul_of_pos_right h_eps_lt_u hk_pos
  have hmul : (edge_vertex_ratio G - (k : ℚ)) * (U.ncard : ℚ) <
      ((G.induce U).edgeFinset.card : ℚ) := by
    nlinarith
  change edge_vertex_ratio G - (k : ℚ) <
    ((G.induce U).edgeFinset.card : ℚ) / (Fintype.card U : ℚ)
  rw [hUcard_fintype]
  rw [lt_div_iff₀ hu_pos]
  exact hmul

theorem minimal_mader_candidate_average_degree_gt {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) {U : Set V}
    [Fintype U] [DecidableRel (G.induce U).Adj]
    (hmin : MinimalFor (fun W => mader_candidate G k W) Set.ncard U) :
    average_degree (G.induce U) > average_degree G - (2 * k : ℚ) ∧
      (2 * k : ℚ) < average_degree G - (2 * k : ℚ) := by
  have hratio := minimal_mader_candidate_edge_vertex_ratio_gt G hk havg hmin
  have hAvgG := average_degree_eq_two_mul_edge_vertex_ratio G
  have hAvgH := average_degree_eq_two_mul_edge_vertex_ratio (G.induce U)
  constructor
  · nlinarith
  · nlinarith

theorem exists_proper_separation_of_delete_vertices_not_connected {V : Type u}
    (H : SimpleGraph V) [Finite V] {S : Set V}
    (hcomp : Nonempty (Sᶜ : Set V))
    (hnot : ¬ (delete_vertices H S).Connected) :
    ∃ A B : Set V, IsProperSeparation H A B ∧ A ∩ B = S := by
  classical
  let D : SimpleGraph (Sᶜ : Set V) := delete_vertices H S
  have hnot_pre : ¬ D.Preconnected := by
    intro hp
    haveI : Nonempty (Sᶜ : Set V) := hcomp
    exact hnot (SimpleGraph.Connected.mk hp)
  rw [SimpleGraph.Preconnected] at hnot_pre
  push Not at hnot_pre
  obtain ⟨a, b, hab⟩ := hnot_pre
  let R : Set (Sᶜ : Set V) := {x | D.Reachable a x}
  let A : Set V := S ∪ (Subtype.val '' R)
  let B : Set V := S ∪ (Subtype.val '' (Rᶜ : Set (Sᶜ : Set V)))
  have haR : a ∈ R := by exact ⟨SimpleGraph.Walk.nil⟩
  have hb_notR : b ∉ R := hab
  refine ⟨A, B, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · ext x
        constructor
        · intro _
          exact Set.mem_univ x
        · intro _
          by_cases hxS : x ∈ S
          · exact Or.inl (Or.inl hxS)
          · let xs : (Sᶜ : Set V) := ⟨x, hxS⟩
            by_cases hxR : xs ∈ R
            · exact Or.inl (Or.inr ⟨xs, hxR, rfl⟩)
            · exact Or.inr (Or.inr ⟨xs, hxR, rfl⟩)
      · intro x y hxA hxnotB hyB hynotA hxy
        have hxnotS : x ∉ S := by
          intro hxS
          exact hxnotB (Or.inl hxS)
        have hynotS : y ∉ S := by
          intro hyS
          exact hynotA (Or.inl hyS)
        have hxR : (⟨x, hxnotS⟩ : (Sᶜ : Set V)) ∈ R := by
          rcases hxA with hxS | hxImg
          · exact False.elim (hxnotS hxS)
          · rcases hxImg with ⟨xr, hxr, hxrval⟩
            have hxreq : xr = ⟨x, hxnotS⟩ := Subtype.ext hxrval
            exact hxreq ▸ hxr
        have hyNotR : (⟨y, hynotS⟩ : (Sᶜ : Set V)) ∉ R := by
          intro hyR
          exact hynotA (Or.inr ⟨⟨y, hynotS⟩, hyR, rfl⟩)
        have hDxy : D.Adj ⟨x, hxnotS⟩ ⟨y, hynotS⟩ := hxy
        have hyR : (⟨y, hynotS⟩ : (Sᶜ : Set V)) ∈ R := by
          exact hxR.trans hDxy.reachable
        exact hyNotR hyR
    · refine ⟨(a : V), ?_⟩
      constructor
      · exact Or.inr ⟨a, haR, rfl⟩
      · intro haB
        rcases haB with haS | haImg
        · exact a.2 haS
        · rcases haImg with ⟨ar, har, harval⟩
          have hareq : ar = a := Subtype.ext harval
          exact (hareq ▸ har) haR
    · refine ⟨(b : V), ?_⟩
      constructor
      · exact Or.inr ⟨b, hb_notR, rfl⟩
      · intro hbA
        rcases hbA with hbS | hbImg
        · exact b.2 hbS
        · rcases hbImg with ⟨br, hbr, hbrval⟩
          have hbreq : br = b := Subtype.ext hbrval
          exact hab (hbreq ▸ hbr)
  · ext x
    constructor
    · intro hx
      rcases hx with ⟨hxA, hxB⟩
      rcases hxA with hxS | hxImg
      · exact hxS
      rcases hxB with hxS | hyImg
      · exact hxS
      rcases hxImg with ⟨xr, hxr, hxval⟩
      rcases hyImg with ⟨yr, hyr, hyval⟩
      have hxyr : xr = yr := Subtype.ext (hxval.trans hyval.symm)
      exact False.elim ((hxyr ▸ hyr) hxr)
    · intro hxS
      exact ⟨Or.inl hxS, Or.inl hxS⟩

theorem isProperSeparation_symm {V : Type u} (H : SimpleGraph V) {A B : Set V}
    (hsep : IsProperSeparation H A B) :
    IsProperSeparation H B A := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Set.union_comm]
      exact hsep.1.1
    · intro b a hbB hbnotA haA hanotB hba
      exact hsep.1.2 haA hanotB hbB hbnotA hba.symm
  · exact hsep.2.2
  · exact hsep.2.1

theorem separation_side_ncard_gt_of_minDegree_gt {V : Type u} (H : SimpleGraph V)
    [Fintype V] [DecidableRel H.Adj] {A B : Set V} {eps : ℚ}
    (hsep : IsProperSeparation H A B)
    (hdeg : ∀ v : V, eps < (H.degree v : ℚ)) :
    eps < (A.ncard : ℚ) := by
  classical
  obtain ⟨v, hvA, hvnotB⟩ := hsep.2.1
  have hsub : H.neighborSet v ⊆ A := by
    intro w hw
    have hwAdj : H.Adj v w := (SimpleGraph.mem_neighborSet H v w).mp hw
    have hw_union : w ∈ A ∪ B := by
      have : w ∈ Set.univ := Set.mem_univ w
      rw [← hsep.1.1] at this
      exact this
    rcases hw_union with hwA | hwB
    · exact hwA
    · by_contra hnotA
      exact hsep.1.2 hvA hvnotB hwB hnotA hwAdj
  have hdeg_le_ncard : H.degree v ≤ A.ncard := by
    have hncard_le : (H.neighborSet v).ncard ≤ A.ncard := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq] at hncard_le
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hncard_le
    exact hncard_le
  exact lt_of_lt_of_le (hdeg v) (by exact_mod_cast hdeg_le_ncard)

theorem minimal_mader_candidate_delete_vertices_connected {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {k : ℕ} (hk : k ≠ 0)
    (havg : (4 * k : ℚ) < average_degree G) {U : Set V}
    [Fintype U] [DecidableRel (G.induce U).Adj]
    (hmin : MinimalFor (fun W => mader_candidate G k W) Set.ncard U) :
    ∀ S : Set U, S.ncard < k + 1 → (delete_vertices (G.induce U) S).Connected := by
  classical
  intro S hSsmall
  by_contra hnotconn
  let H : SimpleGraph U := G.induce U
  have horderU : k + 1 < Nat.card U := minimal_mader_candidate_order_gt G hk havg hmin
  have hS_ne_univ : S ≠ Set.univ := by
    intro hSuniv
    have hScard : S.ncard = Nat.card U := by
      rw [hSuniv, Set.ncard_univ]
    omega
  have hcomp : Nonempty (Sᶜ : Set U) := by
    obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hS_ne_univ
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨A, B, hsep, hAB⟩ :=
    exists_proper_separation_of_delete_vertices_not_connected H hcomp hnotconn
  have heps_gt : (2 * k : ℚ) < edge_vertex_ratio G := by
    have htmp : (4 * k : ℚ) < 2 * edge_vertex_ratio G := by
      rwa [average_degree_eq_two_mul_edge_vertex_ratio G] at havg
    nlinarith
  have heps_pos : (0 : ℚ) < edge_vertex_ratio G := by
    have hkpos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    nlinarith
  have hdeg : ∀ v : U, edge_vertex_ratio G < (H.degree v : ℚ) :=
    minimal_mader_candidate_degree_gt G hk havg hmin
  have hA_gt_eps : edge_vertex_ratio G < (A.ncard : ℚ) :=
    separation_side_ncard_gt_of_minDegree_gt H hsep hdeg
  have hB_gt_eps : edge_vertex_ratio G < (B.ncard : ℚ) :=
    separation_side_ncard_gt_of_minDegree_gt H (isProperSeparation_symm H hsep) hdeg
  have hA_order : 2 * k ≤ (mader_liftSet U A).ncard := by
    rw [mader_liftSet_ncard]
    have hltq : (2 * k : ℚ) < (A.ncard : ℚ) := lt_trans heps_gt hA_gt_eps
    exact Nat.le_of_lt (by exact_mod_cast hltq)
  have hB_order : 2 * k ≤ (mader_liftSet U B).ncard := by
    rw [mader_liftSet_ncard]
    have hltq : (2 * k : ℚ) < (B.ncard : ℚ) := lt_trans heps_gt hB_gt_eps
    exact Nat.le_of_lt (by exact_mod_cast hltq)
  have hA_lt_U_card : A.ncard < Nat.card U := by
    have hAssub : A ⊂ Set.univ := by
      rw [Set.ssubset_univ_iff]
      intro hAuniv
      obtain ⟨b, hbB, hbnotA⟩ := hsep.2.2
      exact hbnotA (by rw [hAuniv]; exact Set.mem_univ b)
    have hlt := Set.ncard_lt_ncard hAssub
    rwa [Set.ncard_univ] at hlt
  have hB_lt_U_card : B.ncard < Nat.card U := by
    have hBssub : B ⊂ Set.univ := by
      rw [Set.ssubset_univ_iff]
      intro hBuniv
      obtain ⟨a, haA, hanotB⟩ := hsep.2.1
      exact hanotB (by rw [hBuniv]; exact Set.mem_univ a)
    have hlt := Set.ncard_lt_ncard hBssub
    rwa [Set.ncard_univ] at hlt
  have hUcard_eq : Nat.card U = U.ncard := Nat.card_coe_set_eq U
  have hA_lt_U : (mader_liftSet U A).ncard < U.ncard := by
    rw [mader_liftSet_ncard]
    rwa [hUcard_eq] at hA_lt_U_card
  have hB_lt_U : (mader_liftSet U B).ncard < U.ncard := by
    rw [mader_liftSet_ncard]
    rwa [hUcard_eq] at hB_lt_U_card
  have hA_not_candidate : ¬ mader_candidate G k (mader_liftSet U A) := by
    intro hcand
    have hUle := hmin.2 hcand hA_lt_U.le
    omega
  have hB_not_candidate : ¬ mader_candidate G k (mader_liftSet U B) := by
    intro hcand
    have hUle := hmin.2 hcand hB_lt_U.le
    omega
  have hA_edges_le :
      (Nat.card (H.induce A).edgeSet : ℚ) ≤
        edge_vertex_ratio G * ((A.ncard : ℚ) - (k : ℚ)) := by
    apply le_of_not_gt
    intro hdense
    apply hA_not_candidate
    refine ⟨hA_order, ?_⟩
    rw [mader_liftSet_ncard]
    rw [edgeSet_nat_card_induce_mader_liftSet]
    exact hdense
  have hB_edges_le :
      (Nat.card (H.induce B).edgeSet : ℚ) ≤
        edge_vertex_ratio G * ((B.ncard : ℚ) - (k : ℚ)) := by
    apply le_of_not_gt
    intro hdense
    apply hB_not_candidate
    refine ⟨hB_order, ?_⟩
    rw [mader_liftSet_ncard]
    rw [edgeSet_nat_card_induce_mader_liftSet]
    exact hdense
  have hsplit_nat := edgeSet_nat_card_le_separation_sides H hsep.1
  have hsplit : (Nat.card H.edgeSet : ℚ) ≤
      (Nat.card (H.induce A).edgeSet : ℚ) +
        (Nat.card (H.induce B).edgeSet : ℚ) := by
    exact_mod_cast hsplit_nat
  have hH_upper : (Nat.card H.edgeSet : ℚ) ≤
      edge_vertex_ratio G * ((A.ncard : ℚ) - (k : ℚ)) +
        edge_vertex_ratio G * ((B.ncard : ℚ) - (k : ℚ)) := by
    nlinarith
  have hS_le_k : S.ncard ≤ k := by omega
  have hABsum_nat : A.ncard + B.ncard = Nat.card U + S.ncard := by
    have hsum := Set.ncard_union_add_ncard_inter A B
    rw [hsep.1.1, hAB, Set.ncard_univ] at hsum
    omega
  have hABsum_q : (A.ncard : ℚ) + (B.ncard : ℚ) = (U.ncard : ℚ) + (S.ncard : ℚ) := by
    have htmp : (A.ncard : ℚ) + (B.ncard : ℚ) =
        (Nat.card U : ℚ) + (S.ncard : ℚ) := by
      exact_mod_cast hABsum_nat
    rw [hUcard_eq] at htmp
    exact htmp
  have hS_le_k_q : (S.ncard : ℚ) ≤ (k : ℚ) := by exact_mod_cast hS_le_k
  have hsep_surplus_nonpos : (S.ncard : ℚ) - (k : ℚ) ≤ 0 := by nlinarith
  have hmul_surplus_nonpos :
      edge_vertex_ratio G * ((S.ncard : ℚ) - (k : ℚ)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos heps_pos.le hsep_surplus_nonpos
  have hside_upper :
      edge_vertex_ratio G * ((A.ncard : ℚ) - (k : ℚ)) +
        edge_vertex_ratio G * ((B.ncard : ℚ) - (k : ℚ)) ≤
          edge_vertex_ratio G * ((U.ncard : ℚ) - (k : ℚ)) := by
    nlinarith
  have hU_dense :
      edge_vertex_ratio G * ((U.ncard : ℚ) - (k : ℚ)) < (Nat.card H.edgeSet : ℚ) :=
    hmin.1.2
  nlinarith

end Chapter01
end Diestel
