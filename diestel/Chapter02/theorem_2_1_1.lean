import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

namespace theorem_2_1_1_aux

variable {V : Type u} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]

private lemma matching_edgeSet_ncard_le_cover_ncard
    {M : G.Subgraph} {C : Set V}
    (hM : M.IsMatching) (hC : G.IsVertexCover C) :
    M.edgeSet.ncard ≤ C.ncard := by
  classical
  have hEndpoint (e : M.edgeSet) : ∃ x : V, x ∈ C ∧ x ∈ (e.1 : Sym2 V) := by
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | h v w =>
      have hMadj : M.Adj v w := by
        exact SimpleGraph.Subgraph.mem_edgeSet.mp he
      rcases hC (M.adj_sub hMadj) with hv | hw
      · exact ⟨v, hv, by simp [Sym2.mem_iff]⟩
      · exact ⟨w, hw, by simp [Sym2.mem_iff]⟩
  let f : M.edgeSet → C := fun e => ⟨Classical.choose (hEndpoint e),
    (Classical.choose_spec (hEndpoint e)).1⟩
  have hf_mem (e : M.edgeSet) : (f e : V) ∈ (e.1 : Sym2 V) :=
    (Classical.choose_spec (hEndpoint e)).2
  have hf_inj : Function.Injective f := by
    intro e e' heq
    apply Subtype.ext
    have hx : (f e : V) = (f e' : V) := congr_arg Subtype.val heq
    have hxe : (f e : V) ∈ (e.1 : Sym2 V) := hf_mem e
    have hxe' : (f e : V) ∈ (e'.1 : Sym2 V) := by
      simpa [hx] using hf_mem e'
    rcases Sym2.mem_iff_exists.mp hxe with ⟨y, hy⟩
    rcases Sym2.mem_iff_exists.mp hxe' with ⟨z, hz⟩
    have hey : M.Adj (f e : V) y := by
      simpa [hy, SimpleGraph.Subgraph.mem_edgeSet] using e.2
    have hez : M.Adj (f e : V) z := by
      simpa [hz, SimpleGraph.Subgraph.mem_edgeSet] using e'.2
    have hyz : y = z := hM.eq_of_adj_left hey hez
    simpa [hy, hz, hyz]
  have hcard : Nat.card M.edgeSet ≤ Nat.card C :=
    Nat.card_le_card_of_injective f hf_inj
  calc
    M.edgeSet.ncard = M.edgeSet.toFinset.card := Set.ncard_eq_toFinset_card' M.edgeSet
    _ = Fintype.card M.edgeSet := Set.toFinset_card M.edgeSet
    _ = Nat.card M.edgeSet := (Nat.card_eq_fintype_card).symm
    _ ≤ Nat.card C := hcard
    _ = Fintype.card C := Nat.card_eq_fintype_card
    _ = C.toFinset.card := (Set.toFinset_card C).symm
    _ = C.ncard := (Set.ncard_eq_toFinset_card' C).symm

private lemma bot_isMatching : (⊥ : G.Subgraph).IsMatching := by
  intro v hv
  simpa [SimpleGraph.Subgraph.verts_bot] using hv

private lemma bot_edgeSet_ncard : (⊥ : G.Subgraph).edgeSet.ncard = 0 := by
  simp [SimpleGraph.Subgraph.edgeSet_bot]

private lemma matchingNumber_le_cover_ncard {C : Set V}
    (hC : G.IsVertexCover C) : matchingNumber G ≤ C.ncard := by
  classical
  let p : ℕ → Prop := fun n => ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card M.edgeSet = n
  have hp0 : p 0 := by
    refine ⟨⊥, bot_isMatching G, ?_⟩
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card (⊥ : G.Subgraph).edgeSet,
      ← Set.ncard_eq_toFinset_card' (⊥ : G.Subgraph).edgeSet,
      bot_edgeSet_ncard (G := G)]
  have hpmax : p (matchingNumber G) := by
    simpa [matchingNumber, p] using
      (Nat.findGreatest_spec (P := p) (n := G.edgeFinset.card) (m := 0) (Nat.zero_le _) hp0)
  rcases hpmax with ⟨M, hM, hcard⟩
  calc
    matchingNumber G = Nat.card M.edgeSet := hcard.symm
    _ = M.edgeSet.ncard := by
      rw [Nat.card_eq_fintype_card, ← Set.toFinset_card M.edgeSet,
        ← Set.ncard_eq_toFinset_card' M.edgeSet]
    _ ≤ C.ncard := matching_edgeSet_ncard_le_cover_ncard G hM hC

private lemma matchingNumber_le_vertexCoverNum :
    (matchingNumber G : ℕ∞) ≤ SimpleGraph.vertexCoverNum G := by
  classical
  rw [SimpleGraph.vertexCoverNum]
  refine le_iInf fun C => ?_
  refine le_iInf fun hC => ?_
  have hnat : matchingNumber G ≤ C.ncard := matchingNumber_le_cover_ncard G hC
  have henc : C.encard = (C.ncard : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card C, Set.ncard_eq_toFinset_card' C]
  exact (ENat.coe_le_coe.mpr hnat).trans_eq henc.symm

private lemma min_cover_ncard_le {C D : Set V}
    (hCmin : C.encard = SimpleGraph.vertexCoverNum G) (hD : G.IsVertexCover D) :
    C.ncard ≤ D.ncard := by
  classical
  have hCD : C.encard ≤ D.encard := by
    rw [hCmin]
    exact hD.vertexCoverNum_le
  have hCenc : C.encard = (C.ncard : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card C, Set.ncard_eq_toFinset_card' C]
  have hDenc : D.encard = (D.ncard : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card D, Set.ncard_eq_toFinset_card' D]
  exact ENat.coe_le_coe.mp (by simpa [hCenc, hDenc] using hCD)

private lemma min_cover_hall_left {A B C S : Set V}
    (hAB : G.IsBipartiteWith A B)
    (hCmin : C.encard = SimpleGraph.vertexCoverNum G)
    (hCcover : G.IsVertexCover C)
    (hS : S ⊆ C ∩ A) :
    S.ncard ≤
      (⋃ x ∈ S, (G.between (C ∩ A) (B \ (C ∩ B))).neighborSet x).ncard := by
  classical
  let X : Set V := C ∩ A
  let Y : Set V := C ∩ B
  let Q : Set V := B \ Y
  let H : SimpleGraph V := G.between X Q
  let N : Set V := ⋃ x ∈ S, H.neighborSet x
  let D : Set V := (C \ S) ∪ N
  have hSX : S ⊆ X := hS
  have hSC : S ⊆ C := fun v hv => (hSX hv).1
  have hXQ : Disjoint X Q := by
    refine Set.disjoint_left.mpr ?_
    intro v hvX hvQ
    exact hvQ.2 ⟨hvX.1, hvQ.1⟩
  have hH : H.IsBipartiteWith X Q := SimpleGraph.between_isBipartiteWith hXQ
  have hNQ : N ⊆ Q := by
    intro v hv
    rcases Set.mem_iUnion.mp hv with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxS, hvN⟩
    exact hH.mem_of_mem_adj (hSX hxS) (by simpa [SimpleGraph.mem_neighborSet] using hvN)
  have hNC : Disjoint N C := by
    refine Set.disjoint_left.mpr ?_
    intro v hvN hvC
    have hvQ : v ∈ Q := hNQ hvN
    exact hvQ.2 ⟨hvC, hvQ.1⟩
  have hDN : Disjoint (C \ S) N := by
    exact Set.disjoint_of_subset_left (Set.diff_subset : C \ S ⊆ C) hNC.symm
  have hDcover : G.IsVertexCover D := by
    intro u v huv
    rcases hCcover huv with huC | hvC
    · by_cases huS : u ∈ S
      · right
        by_cases hvC' : v ∈ C
        · left
          have hvB : v ∈ B := hAB.mem_of_mem_adj (hSX huS).2 huv
          exact ⟨hvC', fun hvS => (Set.disjoint_left.mp hAB.disjoint (hSX hvS).2) hvB⟩
        · right
          refine Set.mem_iUnion.mpr ⟨u, ?_⟩
          refine Set.mem_iUnion.mpr ⟨huS, ?_⟩
          have hvB : v ∈ B := hAB.mem_of_mem_adj (hSX huS).2 huv
          have hvQ : v ∈ Q := ⟨hvB, fun hvY => hvC' hvY.1⟩
          have hHuv : H.Adj u v := by
            exact ⟨huv, Or.inl ⟨hSX huS, hvQ⟩⟩
          simpa [SimpleGraph.mem_neighborSet] using hHuv
      · left
        left
        exact ⟨huC, huS⟩
    · by_cases hvS : v ∈ S
      · left
        by_cases huC' : u ∈ C
        · left
          have huB : u ∈ B := hAB.mem_of_mem_adj (hSX hvS).2 huv.symm
          exact ⟨huC', fun huS => (Set.disjoint_left.mp hAB.disjoint (hSX huS).2) huB⟩
        · right
          refine Set.mem_iUnion.mpr ⟨v, ?_⟩
          refine Set.mem_iUnion.mpr ⟨hvS, ?_⟩
          have huB : u ∈ B := hAB.mem_of_mem_adj (hSX hvS).2 huv.symm
          have huQ : u ∈ Q := ⟨huB, fun huY => huC' huY.1⟩
          have hHvu : H.Adj v u := by
            exact ⟨huv.symm, Or.inl ⟨hSX hvS, huQ⟩⟩
          simpa [SimpleGraph.mem_neighborSet] using hHvu
      · right
        left
        exact ⟨hvC, hvS⟩
  have hmin : C.ncard ≤ D.ncard := min_cover_ncard_le G hCmin hDcover
  have hDcard : D.ncard = (C \ S).ncard + N.ncard := by
    simpa [D] using Set.ncard_union_eq hDN
  have hdiff : (C \ S).ncard = C.ncard - S.ncard := by
    simpa using Set.ncard_diff hSC
  have hSleC : S.ncard ≤ C.ncard := Set.ncard_mono hSC
  have hineq : C.ncard ≤ C.ncard - S.ncard + N.ncard := by
    simpa [hDcard, hdiff] using hmin
  have hSN : S.ncard ≤ N.ncard := by
    omega
  simpa [X, Y, Q, H, N] using hSN

private lemma exists_matching_cover_left {A B C : Set V}
    (hAB : G.IsBipartiteWith A B)
    (hCmin : C.encard = SimpleGraph.vertexCoverNum G)
    (hCcover : G.IsVertexCover C) :
    ∃ M : (G.between (C ∩ A) (B \ (C ∩ B))).Subgraph,
      (C ∩ A) ⊆ M.verts ∧ M.IsMatching := by
  classical
  let X : Set V := C ∩ A
  let Y : Set V := C ∩ B
  let Q : Set V := B \ Y
  let H : SimpleGraph V := G.between X Q
  have hXQ : Disjoint X Q := by
    refine Set.disjoint_left.mpr ?_
    intro v hvX hvQ
    exact hvQ.2 ⟨hvX.1, hvQ.1⟩
  have hH : H.IsBipartiteWith X Q := SimpleGraph.between_isBipartiteWith hXQ
  haveI : H.LocallyFinite := fun v => Fintype.ofFinite (H.neighborSet v)
  simpa [X, Y, Q, H] using
    SimpleGraph.exists_isMatching_of_forall_ncard_le (G := H) (p₁ := X) (p₂ := Q) hH
      (fun S hS => by
        simpa [X, Y, Q, H] using min_cover_hall_left G hAB hCmin hCcover hS)

private lemma left_ncard_le_matching_edgeSet_ncard {P Q : Set V}
    {M : (G.between P Q).Subgraph} (hPQ : Disjoint P Q)
    (hM : M.IsMatching) (hP : P ⊆ M.verts) :
    P.ncard ≤ M.edgeSet.ncard := by
  classical
  let H : SimpleGraph V := G.between P Q
  let mate : P → V := fun p => Classical.choose (hM (hP p.2))
  have hmate_adj (p : P) : M.Adj p.1 (mate p) :=
    (Classical.choose_spec (hM (hP p.2))).1
  have hmate_mem_Q (p : P) : mate p ∈ Q := by
    have hHadj : H.Adj p.1 (mate p) := M.adj_sub (hmate_adj p)
    rcases (SimpleGraph.between_adj.mp hHadj).2 with h | h
    · exact h.2
    · exact False.elim ((Set.disjoint_left.mp hPQ p.2) h.1)
  let f : P → M.edgeSet := fun p => hM.toEdge ⟨p.1, hP p.2⟩
  have hf_inj : Function.Injective f := by
    intro p p' hpp'
    apply Subtype.ext
    have hf_p : f p = ⟨s(p.1, mate p), hmate_adj p⟩ :=
      hM.toEdge_eq_of_adj (hP p.2) (hmate_adj p)
    have hf_p' : f p' = ⟨s(p'.1, mate p'), hmate_adj p'⟩ :=
      hM.toEdge_eq_of_adj (hP p'.2) (hmate_adj p')
    have hp_mem_f : (p.1 : V) ∈ (f p).1 := by
      rw [hf_p]
      simp [Sym2.mem_iff]
    have hp_mem_f' : (p.1 : V) ∈ (f p').1 := by
      simpa [hpp'] using hp_mem_f
    have hp_mem_pair : (p.1 : V) ∈ (s(p'.1, mate p') : Sym2 V) := by
      simpa [hf_p'] using hp_mem_f'
    rcases (by simpa [Sym2.mem_iff, eq_comm] using hp_mem_pair :
        p.1 = p'.1 ∨ p.1 = mate p') with hp_eq | hp_mate
    · exact hp_eq
    · exact False.elim ((Set.disjoint_left.mp hPQ p.2) (hp_mate ▸ hmate_mem_Q p'))
  have hcard : Nat.card P ≤ Nat.card M.edgeSet :=
    Nat.card_le_card_of_injective f hf_inj
  calc
    P.ncard = P.toFinset.card := Set.ncard_eq_toFinset_card' P
    _ = Fintype.card P := Set.toFinset_card P
    _ = Nat.card P := (Nat.card_eq_fintype_card).symm
    _ ≤ Nat.card M.edgeSet := hcard
    _ = Fintype.card M.edgeSet := Nat.card_eq_fintype_card
    _ = M.edgeSet.toFinset.card := (Set.toFinset_card M.edgeSet).symm
    _ = M.edgeSet.ncard := (Set.ncard_eq_toFinset_card' M.edgeSet).symm

private lemma edgeSet_map_ofLE_eq {H : SimpleGraph V} (hHG : H ≤ G)
    (M : H.Subgraph) :
    (M.map (SimpleGraph.Hom.ofLE hHG)).edgeSet = M.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h v w =>
    simp [SimpleGraph.Hom.ofLE]

private lemma support_map_between_subset {P Q : Set V}
    (M : (G.between P Q).Subgraph) :
    (M.map (SimpleGraph.Hom.ofLE SimpleGraph.between_le)).support ⊆ P ∪ Q := by
  intro v hv
  rcases (SimpleGraph.Subgraph.mem_support _).mp hv with ⟨w, hvw⟩
  rw [SimpleGraph.Subgraph.map_adj] at hvw
  rcases hvw with ⟨v', w', hv'w', rfl, rfl⟩
  have hHadj : (G.between P Q).Adj v' w' := M.adj_sub hv'w'
  rcases (SimpleGraph.between_adj.mp hHadj).2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private lemma disjoint_konig_sides {A B C : Set V}
    (hAB : G.IsBipartiteWith A B) :
    Disjoint ((C ∩ A) ∪ (B \ (C ∩ B))) ((C ∩ B) ∪ (A \ (C ∩ A))) := by
  refine Set.disjoint_left.mpr ?_
  intro v hv₁ hv₂
  rcases hv₁ with hvX | hvQx
  · rcases hv₂ with hvY | hvQy
    · exact (Set.disjoint_left.mp hAB.disjoint hvX.2) hvY.2
    · exact hvQy.2 hvX
  · rcases hv₂ with hvY | hvQy
    · exact hvQx.2 hvY
    · exact (Set.disjoint_left.mp hAB.disjoint hvQy.1) hvQx.1

private lemma cover_eq_inter_union {A B C : Set V}
    (hcover : A ∪ B = Set.univ) :
    C = (C ∩ A) ∪ (C ∩ B) := by
  ext v
  constructor
  · intro hvC
    have hvAB : v ∈ A ∪ B := by
      simpa [hcover] using (Set.mem_univ v)
    rcases hvAB with hvA | hvB
    · exact Or.inl ⟨hvC, hvA⟩
    · exact Or.inr ⟨hvC, hvB⟩
  · rintro (hv | hv) <;> exact hv.1

private lemma inter_left_right_disjoint {A B C : Set V}
    (hAB : G.IsBipartiteWith A B) :
    Disjoint (C ∩ A) (C ∩ B) := by
  refine Set.disjoint_left.mpr ?_
  intro v hvA hvB
  exact (Set.disjoint_left.mp hAB.disjoint hvA.2) hvB.2

private lemma cover_ncard_eq_inter_add {A B C : Set V}
    (hAB : G.IsBipartiteWith A B) (hcover : A ∪ B = Set.univ) :
    C.ncard = (C ∩ A).ncard + (C ∩ B).ncard := by
  calc
    C.ncard = ((C ∩ A) ∪ (C ∩ B)).ncard := by
      exact congrArg Set.ncard (cover_eq_inter_union (A := A) (B := B) (C := C) hcover)
    _ = (C ∩ A).ncard + (C ∩ B).ncard :=
      Set.ncard_union_eq
        (inter_left_right_disjoint (G := G) (A := A) (B := B) (C := C) hAB)
        (Set.toFinite (C ∩ A)) (Set.toFinite (C ∩ B))

private lemma matching_edgeSet_ncard_le_matchingNumber {M : G.Subgraph}
    (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ matchingNumber G := by
  classical
  let p : ℕ → Prop := fun n => ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card M.edgeSet = n
  have hsub : M.edgeSet ⊆ G.edgeSet := by
    exact SimpleGraph.Subgraph.edgeSet_mono (show M ≤ ⊤ from le_top)
  have hcard_sub : Nat.card M.edgeSet ≤ Nat.card G.edgeSet :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have hbound : Nat.card M.edgeSet ≤ G.edgeFinset.card := by
    have hGcard : Nat.card G.edgeSet = G.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    exact hcard_sub.trans_eq hGcard
  have hp : p (Nat.card M.edgeSet) := ⟨M, hM, rfl⟩
  have hfind : Nat.card M.edgeSet ≤ matchingNumber G := by
    simpa [matchingNumber, p] using
      (Nat.le_findGreatest (P := p) (n := G.edgeFinset.card) hbound hp)
  calc
    M.edgeSet.ncard = M.edgeSet.toFinset.card := Set.ncard_eq_toFinset_card' M.edgeSet
    _ = Fintype.card M.edgeSet := Set.toFinset_card M.edgeSet
    _ = Nat.card M.edgeSet := (Nat.card_eq_fintype_card).symm
    _ ≤ matchingNumber G := hfind

end theorem_2_1_1_aux

/--
Diestel, Theorem 2.1.1 (Konig).
Natural-language statement:
In a finite bipartite graph, the maximum cardinality of a matching equals
the minimum cardinality of a vertex cover of its edges.
-/
theorem theorem_2_1_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (A B : Set V) :
  G.IsBipartiteWith A B →
    A ∪ B = Set.univ →
      (matchingNumber G : ℕ∞) = SimpleGraph.vertexCoverNum G := by
  classical
  intro hAB hcover
  obtain ⟨C, hCmin, hCcover⟩ := SimpleGraph.vertexCoverNum_exists G
  obtain ⟨Mx0, hXverts, hMx0⟩ :=
    theorem_2_1_1_aux.exists_matching_cover_left (G := G) (A := A) (B := B) (C := C)
      hAB hCmin hCcover
  obtain ⟨My0, hYverts, hMy0⟩ :=
    theorem_2_1_1_aux.exists_matching_cover_left (G := G) (A := B) (B := A) (C := C)
      hAB.symm hCmin hCcover
  let Mx : G.Subgraph := Mx0.map (SimpleGraph.Hom.ofLE SimpleGraph.between_le)
  let My : G.Subgraph := My0.map (SimpleGraph.Hom.ofLE SimpleGraph.between_le)
  let M : G.Subgraph := Mx ⊔ My
  have hMx : Mx.IsMatching := by
    simpa [Mx] using hMx0.map_ofLE (SimpleGraph.between_le (G := G))
  have hMy : My.IsMatching := by
    simpa [My] using hMy0.map_ofLE (SimpleGraph.between_le (G := G))
  have hMxSupp :
      Mx.support ⊆ (C ∩ A) ∪ (B \ (C ∩ B)) := by
    simpa [Mx] using theorem_2_1_1_aux.support_map_between_subset
      (G := G) (P := C ∩ A) (Q := B \ (C ∩ B)) Mx0
  have hMySupp :
      My.support ⊆ (C ∩ B) ∪ (A \ (C ∩ A)) := by
    simpa [My] using theorem_2_1_1_aux.support_map_between_subset
      (G := G) (P := C ∩ B) (Q := A \ (C ∩ A)) My0
  have hsuppDisj : Disjoint Mx.support My.support :=
    Set.disjoint_of_subset hMxSupp hMySupp
      (theorem_2_1_1_aux.disjoint_konig_sides (G := G) (A := A) (B := B) (C := C) hAB)
  have hM : M.IsMatching := by
    simpa [M] using hMx.sup hMy hsuppDisj
  have hvertsDisj : Disjoint Mx.verts My.verts := by
    rwa [← hMx.support_eq_verts, ← hMy.support_eq_verts]
  have hSubDisj : Disjoint Mx My := by
    rw [← SimpleGraph.Subgraph.disjoint_verts_iff_disjoint]
    exact hvertsDisj
  have hedgeDisj : Disjoint Mx.edgeSet My.edgeSet :=
    Disjoint.edgeSet hSubDisj
  have hXQ : Disjoint (C ∩ A) (B \ (C ∩ B)) := by
    refine Set.disjoint_left.mpr ?_
    intro v hvX hvQ
    exact hvQ.2 ⟨hvX.1, hvQ.1⟩
  have hYQ : Disjoint (C ∩ B) (A \ (C ∩ A)) := by
    refine Set.disjoint_left.mpr ?_
    intro v hvY hvQ
    exact hvQ.2 ⟨hvY.1, hvQ.1⟩
  have hXle0 :
      (C ∩ A).ncard ≤ Mx0.edgeSet.ncard :=
    theorem_2_1_1_aux.left_ncard_le_matching_edgeSet_ncard
      (G := G) (P := C ∩ A) (Q := B \ (C ∩ B)) hXQ hMx0 hXverts
  have hYle0 :
      (C ∩ B).ncard ≤ My0.edgeSet.ncard :=
    theorem_2_1_1_aux.left_ncard_le_matching_edgeSet_ncard
      (G := G) (P := C ∩ B) (Q := A \ (C ∩ A)) hYQ hMy0 hYverts
  have hMxEdge :
      Mx.edgeSet = Mx0.edgeSet := by
    simpa [Mx] using theorem_2_1_1_aux.edgeSet_map_ofLE_eq
      (G := G) (H := G.between (C ∩ A) (B \ (C ∩ B)))
      (SimpleGraph.between_le (G := G)) Mx0
  have hMyEdge :
      My.edgeSet = My0.edgeSet := by
    simpa [My] using theorem_2_1_1_aux.edgeSet_map_ofLE_eq
      (G := G) (H := G.between (C ∩ B) (A \ (C ∩ A)))
      (SimpleGraph.between_le (G := G)) My0
  have hXle : (C ∩ A).ncard ≤ Mx.edgeSet.ncard := by
    rwa [hMxEdge]
  have hYle : (C ∩ B).ncard ≤ My.edgeSet.ncard := by
    rwa [hMyEdge]
  have hEdgeCard : M.edgeSet.ncard = Mx.edgeSet.ncard + My.edgeSet.ncard := by
    simpa [M, SimpleGraph.Subgraph.edgeSet_sup] using
      Set.ncard_union_eq hedgeDisj (Set.toFinite Mx.edgeSet) (Set.toFinite My.edgeSet)
  have hCcard :
      C.ncard = (C ∩ A).ncard + (C ∩ B).ncard :=
    theorem_2_1_1_aux.cover_ncard_eq_inter_add (G := G) (A := A) (B := B) (C := C)
      hAB hcover
  have hEdgesLower : C.ncard ≤ M.edgeSet.ncard := by
    rw [hCcard, hEdgeCard]
    exact Nat.add_le_add hXle hYle
  have hNatHard : C.ncard ≤ matchingNumber G :=
    hEdgesLower.trans
      (theorem_2_1_1_aux.matching_edgeSet_ncard_le_matchingNumber (G := G) (M := M) hM)
  have hVCeq : SimpleGraph.vertexCoverNum G = (C.ncard : ℕ∞) := by
    have hCenc : C.encard = (C.ncard : ℕ∞) := by
      rw [Set.encard_eq_coe_toFinset_card C, Set.ncard_eq_toFinset_card' C]
    rw [← hCmin, hCenc]
  have hHard : SimpleGraph.vertexCoverNum G ≤ (matchingNumber G : ℕ∞) := by
    rw [hVCeq]
    exact ENat.coe_le_coe.mpr hNatHard
  exact le_antisymm (theorem_2_1_1_aux.matchingNumber_le_vertexCoverNum G) hHard

end Chapter02
end Diestel
