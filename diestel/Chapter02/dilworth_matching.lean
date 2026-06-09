import Chapter02.dilworth_aux
import Mathlib.Order.Preorder.Finite

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

namespace DilworthMatching

/-- The split bipartite graph of a strict order: left `x` is joined to right `y`
when `x < y`. -/
def splitOrderGraph (P : Type u) [LT P] : SimpleGraph (P ⊕ P) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inr y => x < y
    | Sum.inr y, Sum.inl x => x < y
    | _, _ => False
  symm := by
    intro a b h
    cases a <;> cases b <;> simpa using h
  loopless := ⟨fun a => by
    cases a <;> simp⟩

def leftSide (P : Type u) : Set (P ⊕ P) :=
  Set.range Sum.inl

def rightSide (P : Type u) : Set (P ⊕ P) :=
  Set.range Sum.inr

lemma left_union_right (P : Type u) :
    leftSide P ∪ rightSide P = Set.univ := by
  ext x
  cases x <;> simp [leftSide, rightSide]

lemma splitOrderGraph_isBipartiteWith (P : Type u) [LT P] :
    (splitOrderGraph P).IsBipartiteWith (leftSide P) (rightSide P) where
  disjoint := by
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨x, rfl⟩ ⟨y, h⟩
    cases h
  mem_of_adj := by
    intro v w h
    cases v with
    | inl x =>
        cases w with
        | inl y => simpa [splitOrderGraph] using h
        | inr y =>
            exact Or.inl ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    | inr y =>
        cases w with
        | inl x =>
            exact Or.inr ⟨⟨y, rfl⟩, ⟨x, rfl⟩⟩
        | inr z => simpa [splitOrderGraph] using h

def coveredProjectionSet {P : Type u} (C : Set (P ⊕ P)) : Set P :=
  {x | Sum.inl x ∈ C ∨ Sum.inr x ∈ C}

noncomputable def uncoveredBothFinset (P : Type u) [Fintype P] (C : Set (P ⊕ P)) :
    Finset P :=
  by
    classical
    exact Finset.univ.filter fun x => Sum.inl x ∉ C ∧ Sum.inr x ∉ C

lemma mem_uncoveredBothFinset {P : Type u} [Fintype P] (C : Set (P ⊕ P)) (x : P) :
    x ∈ uncoveredBothFinset P C ↔ Sum.inl x ∉ C ∧ Sum.inr x ∉ C := by
  classical
  simp [uncoveredBothFinset]

lemma coveredProjectionSet_ncard_le {P : Type u} [Fintype P]
    (C : Set (P ⊕ P)) :
    (coveredProjectionSet C).ncard ≤ C.ncard := by
  classical
  let f : {x : P // x ∈ coveredProjectionSet C} → C := fun x =>
    if hx : Sum.inl x.1 ∈ C then
      ⟨Sum.inl x.1, hx⟩
    else
      ⟨Sum.inr x.1, Or.resolve_left x.2 hx⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hval : (f a : P ⊕ P) = (f b : P ⊕ P) := congrArg Subtype.val hab
    by_cases ha : Sum.inl a.1 ∈ C
    · by_cases hb : Sum.inl b.1 ∈ C
      · simpa [f, ha, hb] using hval
      · simp [f, ha, hb] at hval
    · by_cases hb : Sum.inl b.1 ∈ C
      · simp [f, ha, hb] at hval
      · simpa [f, ha, hb] using hval
  have hcard : Nat.card {x : P // x ∈ coveredProjectionSet C} ≤ Nat.card C :=
    Nat.card_le_card_of_injective f hf
  calc
    (coveredProjectionSet C).ncard =
        (coveredProjectionSet C).toFinset.card := Set.ncard_eq_toFinset_card' _
    _ = Fintype.card {x : P // x ∈ coveredProjectionSet C} := Set.toFinset_card _
    _ = Nat.card {x : P // x ∈ coveredProjectionSet C} := (Nat.card_eq_fintype_card).symm
    _ ≤ Nat.card C := hcard
    _ = Fintype.card C := Nat.card_eq_fintype_card
    _ = C.toFinset.card := (Set.toFinset_card C).symm
    _ = C.ncard := (Set.ncard_eq_toFinset_card' C).symm

lemma uncoveredBothFinset_card {P : Type u} [Fintype P]
    (C : Set (P ⊕ P)) :
    (uncoveredBothFinset P C).card =
      Nat.card P - (coveredProjectionSet C).ncard := by
  classical
  let U : Set P := {x | Sum.inl x ∉ C ∧ Sum.inr x ∉ C}
  have hU : U = (coveredProjectionSet C)ᶜ := by
    ext x
    simp [U, coveredProjectionSet, not_or]
  have hcardU : (uncoveredBothFinset P C).card = U.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [U, uncoveredBothFinset]
  calc
    (uncoveredBothFinset P C).card = U.ncard := hcardU
    _ = ((coveredProjectionSet C)ᶜ).ncard := by rw [hU]
    _ = Nat.card P - (coveredProjectionSet C).ncard := by
      simpa using Set.ncard_compl (coveredProjectionSet C)

lemma uncoveredBoth_isAntichain {P : Type u} [Fintype P] [PartialOrder P]
    {C : Set (P ⊕ P)} (hC : (splitOrderGraph P).IsVertexCover C) :
    IsAntichainFinset (uncoveredBothFinset P C) := by
  classical
  intro x hx y hy hxy
  have hxC := (mem_uncoveredBothFinset C x).mp hx
  have hyC := (mem_uncoveredBothFinset C y).mp hy
  constructor
  · intro hle
    have hlt : x < y := lt_of_le_of_ne hle hxy
    have hadj : (splitOrderGraph P).Adj (Sum.inl x) (Sum.inr y) := by
      simpa [splitOrderGraph] using hlt
    rcases hC hadj with hxleft | hyright
    · exact hxC.1 hxleft
    · exact hyC.2 hyright
  · intro hle
    have hlt : y < x := lt_of_le_of_ne hle hxy.symm
    have hadj : (splitOrderGraph P).Adj (Sum.inl y) (Sum.inr x) := by
      simpa [splitOrderGraph] using hlt
    rcases hC hadj with hyleft | hxright
    · exact hyC.1 hyleft
    · exact hxC.2 hxright

lemma vertexCover_complement_le_maxAntichainCard {P : Type u}
    [Fintype P] [DecidableEq P] [PartialOrder P]
    {C : Set (P ⊕ P)} (hC : (splitOrderGraph P).IsVertexCover C) :
    Nat.card P - C.ncard ≤ maxAntichainCard P := by
  classical
  have hDle : (coveredProjectionSet C).ncard ≤ C.ncard :=
    coveredProjectionSet_ncard_le C
  have hsub :
      Nat.card P - C.ncard ≤ Nat.card P - (coveredProjectionSet C).ncard :=
    Nat.sub_le_sub_left hDle (Nat.card P)
  have hcard :
      Nat.card P - (coveredProjectionSet C).ncard =
        (uncoveredBothFinset P C).card := by
    rw [uncoveredBothFinset_card]
  calc
    Nat.card P - C.ncard ≤ Nat.card P - (coveredProjectionSet C).ncard := hsub
    _ = (uncoveredBothFinset P C).card := hcard
    _ ≤ maxAntichainCard P :=
      DilworthAux.antichain_card_le_maxAntichainCard
        (uncoveredBoth_isAntichain (P := P) hC)

def Succ {P : Type u} [LT P] (M : (splitOrderGraph P).Subgraph) (x y : P) : Prop :=
  M.Adj (Sum.inl x) (Sum.inr y)

def HasPred {P : Type u} [LT P] (M : (splitOrderGraph P).Subgraph) (y : P) : Prop :=
  ∃ x : P, Succ M x y

noncomputable def sourceFinset (P : Type u) [Fintype P] [LT P]
    (M : (splitOrderGraph P).Subgraph) : Finset P :=
  by
    classical
    exact Finset.univ.filter fun x => ¬ HasPred M x

noncomputable def reachFinset (P : Type u) [Fintype P] [LT P]
    (M : (splitOrderGraph P).Subgraph) (s : P) : Finset P :=
  by
    classical
    exact Finset.univ.filter fun x => Relation.ReflTransGen (Succ M) s x

lemma mem_sourceFinset {P : Type u} [Fintype P] [LT P]
    (M : (splitOrderGraph P).Subgraph) (x : P) :
    x ∈ sourceFinset P M ↔ ¬ HasPred M x := by
  classical
  simp [sourceFinset]

lemma mem_reachFinset {P : Type u} [Fintype P] [LT P]
    (M : (splitOrderGraph P).Subgraph) (s x : P) :
    x ∈ reachFinset P M s ↔ Relation.ReflTransGen (Succ M) s x := by
  classical
  simp [reachFinset]

lemma succ_lt {P : Type u} [LT P] {M : (splitOrderGraph P).Subgraph}
    {x y : P} (hxy : Succ M x y) : x < y := by
  have hG : (splitOrderGraph P).Adj (Sum.inl x) (Sum.inr y) := M.adj_sub hxy
  simpa [splitOrderGraph] using hG

lemma succ_rightUnique {P : Type u} [LT P] {M : (splitOrderGraph P).Subgraph}
    (hM : M.IsMatching) : Relator.RightUnique (Succ M) := by
  intro x y z hxy hxz
  have hsum : Sum.inr y = Sum.inr z := hM.eq_of_adj_left hxy hxz
  simpa using hsum

lemma succ_leftUnique {P : Type u} [LT P] {M : (splitOrderGraph P).Subgraph}
    (hM : M.IsMatching) : Relator.LeftUnique (Succ M) := by
  intro x y z hxz hyz
  have hsum : Sum.inl x = Sum.inl y := hM.eq_of_adj_right hxz hyz
  simpa using hsum

lemma reach_le {P : Type u} [Preorder P] {M : (splitOrderGraph P).Subgraph}
    {x y : P} (hxy : Relation.ReflTransGen (Succ M) x y) : x ≤ y := by
  induction hxy with
  | refl => rfl
  | tail hreach hsucc ih =>
      exact le_trans ih (le_of_lt (succ_lt hsucc))

lemma reachFinset_isChain {P : Type u} [Fintype P] [Preorder P]
    {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) (s : P) :
    IsChainFinset (reachFinset P M s) := by
  classical
  intro x hx y hy
  have hxreach := (mem_reachFinset M s x).mp hx
  have hyreach := (mem_reachFinset M s y).mp hy
  rcases Relation.ReflTransGen.total_of_right_unique (succ_rightUnique hM) hxreach hyreach with
    hxy | hyx
  · exact Or.inl (reach_le hxy)
  · exact Or.inr (reach_le hyx)

lemma exists_source_reaches {P : Type u} [Fintype P] [PartialOrder P]
    {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) (x : P) :
    ∃ s : P, s ∈ sourceFinset P M ∧ Relation.ReflTransGen (Succ M) s x := by
  classical
  let A : Set P := {y | Relation.ReflTransGen (Succ M) y x}
  have hAfinite : A.Finite := Set.toFinite A
  have hAnonempty : A.Nonempty := ⟨x, Relation.ReflTransGen.refl⟩
  obtain ⟨s, hsmin⟩ := hAfinite.exists_minimal hAnonempty
  refine ⟨s, ?_, hsmin.prop⟩
  rw [mem_sourceFinset]
  rintro ⟨z, hzs⟩
  have hzA : z ∈ A := Relation.ReflTransGen.head hzs hsmin.prop
  exact hsmin.not_prop_of_lt (succ_lt hzs) hzA

lemma chainCover_sourceFinset_card_of_matching {P : Type u} [Fintype P]
    [PartialOrder P] {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) :
    ChainCover P (sourceFinset P M).card := by
  classical
  let S := sourceFinset P M
  let e : Fin S.card ≃ S := S.equivFin.symm
  refine ⟨fun i => reachFinset P M (e i).1, ?_, ?_⟩
  · intro i
    exact reachFinset_isChain (M := M) hM (e i).1
  · intro x
    obtain ⟨s, hsS, hsx⟩ := exists_source_reaches (M := M) hM x
    let i : Fin S.card := S.equivFin ⟨s, hsS⟩
    refine ⟨i, ?_⟩
    have hi : (e i).1 = s := by
      simp [e, i]
    simpa [hi] using (mem_reachFinset M s x).mpr hsx

noncomputable def rightMatchedFinset (P : Type u) [Fintype P] [LT P]
    (M : (splitOrderGraph P).Subgraph) : Finset P :=
  by
    classical
    exact Finset.univ.filter fun x => Sum.inr x ∈ M.verts

lemma mem_rightMatchedFinset {P : Type u} [Fintype P] [LT P]
    (M : (splitOrderGraph P).Subgraph) (x : P) :
    x ∈ rightMatchedFinset P M ↔ Sum.inr x ∈ M.verts := by
  classical
  simp [rightMatchedFinset]

lemma hasPred_iff_right_mem_verts {P : Type u} [Fintype P] [LT P]
    {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) (x : P) :
    HasPred M x ↔ Sum.inr x ∈ M.verts := by
  constructor
  · rintro ⟨y, hyx⟩
    exact M.edge_vert hyx.symm
  · intro hx
    obtain ⟨z, hzx, -⟩ := hM hx
    have hG : (splitOrderGraph P).Adj (Sum.inr x) z := M.adj_sub hzx
    cases z with
    | inl y =>
        exact ⟨y, hzx.symm⟩
    | inr y =>
        simpa [splitOrderGraph] using hG

private lemma right_mem_eq_of_edge {P : Type u} [LT P]
    {M : (splitOrderGraph P).Subgraph} {e : M.edgeSet} {x y : P}
    (hx : Sum.inr x ∈ (e.1 : Sym2 (P ⊕ P)))
    (hy : Sum.inr y ∈ (e.1 : Sym2 (P ⊕ P))) : x = y := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      have hG : (splitOrderGraph P).Adj a b := M.adj_sub he
      cases a <;> cases b <;> simp [splitOrderGraph, Sym2.mem_iff] at hG hx hy ⊢
      all_goals subst x; subst y; rfl

private lemma right_mem_toEdge {P : Type u} [LT P]
    {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching)
    {x : P} (hx : Sum.inr x ∈ M.verts) :
    Sum.inr x ∈
      ((hM.toEdge ⟨Sum.inr x, hx⟩).1 : Sym2 (P ⊕ P)) := by
  simp [SimpleGraph.Subgraph.IsMatching.toEdge, Sym2.mem_iff]

private lemma exists_adj_of_mem_edge {P : Type u} [LT P]
    {M : (splitOrderGraph P).Subgraph} {e : Sym2 (P ⊕ P)}
    (he : e ∈ M.edgeSet) {v : P ⊕ P} (hv : v ∈ e) :
    ∃ w : P ⊕ P, M.Adj v w ∧ e = s(v, w) := by
  induction e using Sym2.ind with
  | h a b =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      rw [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨b, he, rfl⟩
      · exact ⟨a, he.symm, Sym2.eq_swap⟩

private lemma exists_right_mem_of_edge {P : Type u} [LT P]
    {M : (splitOrderGraph P).Subgraph} (e : M.edgeSet) :
    ∃ y : P, Sum.inr y ∈ (e.1 : Sym2 (P ⊕ P)) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      have hG : (splitOrderGraph P).Adj a b := M.adj_sub he
      cases a <;> cases b <;> simp [splitOrderGraph, Sym2.mem_iff] at hG ⊢

lemma rightMatchedFinset_card_eq_edgeSet_ncard {P : Type u} [Fintype P]
    [LT P] {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) :
    (rightMatchedFinset P M).card = M.edgeSet.ncard := by
  classical
  let f : rightMatchedFinset P M → M.edgeSet := fun x =>
    hM.toEdge ⟨Sum.inr x.1, (mem_rightMatchedFinset M x.1).mp x.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxmem : Sum.inr x.1 ∈ (f y).1 := by
      rw [← hxy]
      exact right_mem_toEdge hM ((mem_rightMatchedFinset M x.1).mp x.2)
    have hymem : Sum.inr y.1 ∈ (f y).1 :=
      right_mem_toEdge hM ((mem_rightMatchedFinset M y.1).mp y.2)
    exact right_mem_eq_of_edge hxmem hymem
  have hf_surj : Function.Surjective f := by
    intro e
    obtain ⟨y, hy⟩ := exists_right_mem_of_edge e
    have hyverts : Sum.inr y ∈ M.verts :=
      M.mem_verts_of_mem_edge e.2 hy
    refine ⟨⟨y, (mem_rightMatchedFinset M y).mpr hyverts⟩, ?_⟩
    obtain ⟨z, hyz, heq⟩ := exists_adj_of_mem_edge e.2 hy
    apply Subtype.ext
    have hto := hM.toEdge_eq_of_adj hyverts hyz
    simpa [f, heq] using congrArg Subtype.val hto
  have hcard :
      Fintype.card (rightMatchedFinset P M) = Fintype.card M.edgeSet :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  calc
    (rightMatchedFinset P M).card = Fintype.card (rightMatchedFinset P M) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card M.edgeSet := hcard
    _ = M.edgeSet.toFinset.card := (Set.toFinset_card M.edgeSet).symm
    _ = M.edgeSet.ncard := (Set.ncard_eq_toFinset_card' M.edgeSet).symm

lemma sourceFinset_card_eq {P : Type u} [Fintype P] [PartialOrder P]
    {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) :
    (sourceFinset P M).card = Nat.card P - M.edgeSet.ncard := by
  classical
  let predFinset : Finset P := Finset.univ.filter fun x => HasPred M x
  have hpredRight : predFinset = rightMatchedFinset P M := by
    ext x
    simp [predFinset, rightMatchedFinset, hasPred_iff_right_mem_verts hM x]
  have hsum :
      predFinset.card + (sourceFinset P M).card = Fintype.card P := by
    simpa [predFinset, sourceFinset] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P))
        (p := fun x => HasPred M x))
  have hsum' :
      M.edgeSet.ncard + (sourceFinset P M).card = Nat.card P := by
    simpa [hpredRight, rightMatchedFinset_card_eq_edgeSet_ncard hM,
      Nat.card_eq_fintype_card] using hsum
  omega

lemma chainCover_of_matching {P : Type u} [Fintype P] [PartialOrder P]
    {M : (splitOrderGraph P).Subgraph} (hM : M.IsMatching) :
    ChainCover P (Nat.card P - M.edgeSet.ncard) := by
  rw [← sourceFinset_card_eq (P := P) hM]
  exact chainCover_sourceFinset_card_of_matching (P := P) hM

lemma exists_matchingNumber_subgraph {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingNumber G := by
  classical
  let p : ℕ → Prop := fun n => ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card M.edgeSet = n
  have hbotMatching : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simpa [SimpleGraph.Subgraph.verts_bot] using hv
  have hp0 : p 0 := by
    refine ⟨⊥, hbotMatching, ?_⟩
    simp [SimpleGraph.Subgraph.edgeSet_bot]
  have hpmax : p (matchingNumber G) := by
    simpa [matchingNumber, p] using
      (Nat.findGreatest_spec (P := p) (n := G.edgeFinset.card) (m := 0) (Nat.zero_le _) hp0)
  rcases hpmax with ⟨M, hM, hcard⟩
  refine ⟨M, hM, ?_⟩
  calc
    M.edgeSet.ncard = M.edgeSet.toFinset.card := Set.ncard_eq_toFinset_card' M.edgeSet
    _ = Fintype.card M.edgeSet := Set.toFinset_card M.edgeSet
    _ = Nat.card M.edgeSet := (Nat.card_eq_fintype_card).symm
    _ = matchingNumber G := hcard

end DilworthMatching

end Chapter02
end Diestel
