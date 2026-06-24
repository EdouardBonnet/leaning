import TwinWidth.Contraction.Trigraph










namespace TwinWidth
namespace SimpleGraph


noncomputable def redDegree {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  T.redDegree A



def IsInitialState {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T : TrigraphState V) : Prop :=
  T.bags = TrigraphState.singletonBags V ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags →
      (T.blackAdj A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags → ¬ T.redAdj A B)






def IsFinalState {V : Type*} (T : TrigraphState V) : Prop :=
  T.bags.card ≤ 1



def contractionPreimages {V : Type*} [DecidableEq V]
    (A B X : Finset V) : Finset (Finset V) :=
  if X = A ∪ B then {A, B} else {X}







def contractedRed {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.redAdj A Y ∨ T.redAdj B Y ∨ T.blackAdj A Y ≠ T.blackAdj B Y
  else if Y = A ∪ B then
    T.redAdj X A ∨ T.redAdj X B ∨ T.blackAdj X A ≠ T.blackAdj X B
  else
    T.redAdj X Y






def contractedBlack {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.blackAdj A Y ∧ T.blackAdj B Y ∧ ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    T.blackAdj X A ∧ T.blackAdj X B ∧ ¬ contractedRed T A B X Y
  else
    T.blackAdj X Y


def IsContractionStep {V : Type*} [DecidableEq V]
    (T U : TrigraphState V) : Prop :=
  ∃ A ∈ T.bags, ∃ B ∈ T.bags, A ≠ B ∧
    U.bags = insert (A ∪ B) ((T.bags.erase A).erase B) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      (U.redAdj X Y ↔ contractedRed T A B X Y)) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      (U.blackAdj X Y ↔ contractedBlack T A B X Y))

theorem IsContractionStep.bags_card_add_one
    {V : Type*} [DecidableEq V] {T U : TrigraphState V}
    (h : IsContractionStep T U) :
    U.bags.card + 1 = T.bags.card := by
  classical
  rcases h with ⟨A, hA, B, hB, hAB, hbags, _hred, _hblack⟩
  have hB_eraseA : B ∈ T.bags.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hA_not_rest : A ∉ (T.bags.erase A).erase B := by simp
  have hB_not_rest : B ∉ (T.bags.erase A).erase B := by simp
  have hUnion_not_rest : A ∪ B ∉ (T.bags.erase A).erase B := by
    intro hU
    have hUold : A ∪ B ∈ T.bags :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hU).2).2
    have hneA : A ≠ A ∪ B := by
      intro h
      have hBinA : B ⊆ A := by
        intro x hxB
        have hxU : x ∈ A ∪ B := Finset.mem_union_right _ hxB
        simpa [← h] using hxU
      rcases T.bag_nonempty hB with ⟨b, hb⟩
      have hbA : b ∈ A := hBinA hb
      exact (Finset.disjoint_left.mp (T.bag_disjoint hA hB hAB)) hbA hb
    rcases T.bag_nonempty hA with ⟨a, ha⟩
    exact (Finset.disjoint_left.mp (T.bag_disjoint hA hUold hneA))
      ha (Finset.mem_union_left _ ha)
  calc
    U.bags.card + 1
        = (insert (A ∪ B) ((T.bags.erase A).erase B)).card + 1 := by rw [hbags]
    _ = ((T.bags.erase A).erase B).card + 2 := by
        rw [Finset.card_insert_of_notMem hUnion_not_rest]
    _ = (T.bags.erase A).card + 1 := by
        rw [Finset.card_erase_of_mem hB_eraseA]
        have hpos : 0 < (T.bags.erase A).card := Finset.card_pos.mpr ⟨B, hB_eraseA⟩
        omega
    _ = T.bags.card := by
        rw [Finset.card_erase_of_mem hA]
        have hpos : 0 < T.bags.card := Finset.card_pos.mpr ⟨A, hA⟩
        omega


structure ContractionSequence {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) where
  
  stepCount : ℕ
  
  state : ℕ → TrigraphState V
  
  starts : IsInitialState G (state 0)
  
  ends : IsFinalState (state stepCount)
  
  step_contracts : ∀ i, i < stepCount → IsContractionStep (state i) (state (i + 1))
  
  redDegree_le : ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ (state i).bags → redDegree (state i) A ≤ d

namespace ContractionSequence

theorem bags_card_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) {i : ℕ} (hi : i < S.stepCount) :
    (S.state (i + 1)).bags.card + 1 = (S.state i).bags.card :=
  (S.step_contracts i hi).bags_card_add_one

theorem start_bags_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    (S.state 0).bags.card = Fintype.card V := by
  rw [S.starts.1]
  exact TrigraphState.card_singletonBags V



theorem bags_card_add_index
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    ∀ ⦃i : ℕ⦄, i ≤ S.stepCount →
      (S.state i).bags.card + i = Fintype.card V := by
  intro i hi
  induction i with
  | zero =>
      simpa using S.start_bags_card
  | succ i ih =>
      have hlt : i < S.stepCount := by omega
      have hprev : (S.state i).bags.card + i = Fintype.card V := ih (by omega)
      have hstep : (S.state (i + 1)).bags.card + 1 = (S.state i).bags.card :=
        S.bags_card_add_one hlt
      omega



theorem final_bags_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    (S.state S.stepCount).bags.card = 1 := by
  rcases ‹Nonempty V› with ⟨v⟩
  rcases (S.state S.stepCount).bag_cover v with ⟨A, hA, _hvA⟩
  have hpos : 0 < (S.state S.stepCount).bags.card :=
    Finset.card_pos.mpr ⟨A, hA⟩
  have hle : (S.state S.stepCount).bags.card ≤ 1 := S.ends
  omega



theorem stepCount_add_one_eq_card
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (S : ContractionSequence G d) :
    S.stepCount + 1 = Fintype.card V := by
  have hcount := S.bags_card_add_index (i := S.stepCount) le_rfl
  have hfinal := S.final_bags_card_eq_one
  omega

end ContractionSequence



def HasTwinWidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (ContractionSequence G d)





noncomputable def twinWidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact if h : ∃ d, HasTwinWidthAtMost G d then Nat.find h else 0

theorem hasTwinWidthAtMost_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d e : ℕ}
    (h : HasTwinWidthAtMost G d) (hde : d ≤ e) :
    HasTwinWidthAtMost G e := by
  rcases h with ⟨S⟩
  refine ⟨(?_ : ContractionSequence G e)⟩
  exact ContractionSequence.mk S.stepCount S.state S.starts S.ends S.step_contracts
    (fun i hi A hA => le_trans (S.redDegree_le i hi hA) hde)

theorem twinWidth_le_of_hasTwinWidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (h : HasTwinWidthAtMost G d) :
    twinWidth G ≤ d := by
  classical
  have hex : ∃ e, HasTwinWidthAtMost G e := ⟨d, h⟩
  rw [twinWidth, dif_pos hex]
  exact Nat.find_min' hex h

theorem hasTwinWidthAtMost_twinWidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (h : ∃ d, HasTwinWidthAtMost G d) :
    HasTwinWidthAtMost G (twinWidth G) := by
  classical
  rw [twinWidth, dif_pos h]
  exact Nat.find_spec h

end SimpleGraph
end TwinWidth
