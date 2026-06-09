import Chapter01.definitions_ch1
import Mathlib.Data.Fintype.Card

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private def liftSet {V : Type u} (S : Set V) (B : Set S) : Set V :=
  Subtype.val '' B

private noncomputable def induce_liftSet_iso {V : Type u} (G : SimpleGraph V)
    (S : Set V) (B : Set S) :
    G.induce (liftSet S B) ≃g (G.induce S).induce B where
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

private lemma liftSet_univ {V : Type u} (S : Set V) :
    liftSet S (Set.univ : Set S) = S := by
  ext x
  constructor
  · rintro ⟨y, _hy, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

private lemma liftSet_empty {V : Type u} (S : Set V) :
    liftSet S (∅ : Set S) = ∅ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact False.elim hy
  · intro hx
    exact False.elim hx

private theorem connected_vertex_enumeration {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    G.Connected →
      ∃ A : ℕ → Set V,
        A 0 = ∅ ∧
          A (Fintype.card V) = Set.univ ∧
            ∀ i : ℕ, i < Fintype.card V →
              A i ⊆ A (i + 1) ∧
                (A (i + 1)).ncard = i + 1 ∧
                  (G.induce (A (i + 1))).Connected := by
  classical
  refine (Fintype.induction_subsingleton_or_nontrivial
    (P := fun α _ =>
      ∀ G : SimpleGraph α,
        G.Connected →
          ∃ A : ℕ → Set α,
            A 0 = ∅ ∧
              A (Fintype.card α) = Set.univ ∧
                ∀ i : ℕ, i < Fintype.card α →
                  A i ⊆ A (i + 1) ∧
                    (A (i + 1)).ncard = i + 1 ∧
                      (G.induce (A (i + 1))).Connected)
    V ?base ?step) G
  · intro α _ hsub G hconn
    haveI : Nonempty α := hconn.nonempty
    haveI : Unique α := {
      default := Classical.choice hconn.nonempty
      uniq := fun x => Subsingleton.elim x (Classical.choice hconn.nonempty) }
    let A : ℕ → Set α := fun i => if i = 0 then ∅ else Set.univ
    refine ⟨A, ?_, ?_, ?_⟩
    · simp [A]
    · have hcard : Fintype.card α = 1 := Fintype.card_unique
      simp [A, hcard]
    · intro i hi
      have hcard : Fintype.card α = 1 := Fintype.card_unique
      have hi0 : i = 0 := by omega
      subst i
      constructor
      · intro x hx
        simp [A] at hx
      constructor
      · simp [A, Set.ncard_univ, hcard]
      · simpa [A] using (SimpleGraph.induceUnivIso G).connected_iff.mpr hconn
  · intro α _ hnontriv ih G hconn
    obtain ⟨v, hvconn⟩ :=
      hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let S : Set α := {v}ᶜ
    have hcardS : Fintype.card S = Fintype.card α - 1 := by
      rw [Fintype.card_compl_set ({v} : Set α)]
      simp
    have hcardα : Fintype.card α = Fintype.card S + 1 := by
      have hpos : 0 < Fintype.card α := Fintype.card_pos
      omega
    have hcardS_lt : Fintype.card S < Fintype.card α := by omega
    obtain ⟨B, hB0, hBcard, hBstep⟩ :=
      ih S hcardS_lt (G.induce S) hvconn
    let A : ℕ → Set α :=
      fun i => if i ≤ Fintype.card S then liftSet S (B i) else Set.univ
    refine ⟨A, ?_, ?_, ?_⟩
    · have h0 : 0 ≤ Fintype.card S := Nat.zero_le _
      rw [show A 0 = liftSet S (B 0) by
        dsimp [A], hB0, liftSet_empty]
    · have hnot : ¬Fintype.card α ≤ Fintype.card S := by omega
      dsimp [A]
      rw [if_neg hnot]
    · intro i hi
      by_cases hiS : i < Fintype.card S
      · have hi_le : i ≤ Fintype.card S := le_of_lt hiS
        have hisucc_le : i + 1 ≤ Fintype.card S := Nat.succ_le_of_lt hiS
        have hAi : A i = liftSet S (B i) := by
          dsimp [A]
          rw [if_pos hi_le]
        have hAsucc : A (i + 1) = liftSet S (B (i + 1)) := by
          dsimp [A]
          rw [if_pos hisucc_le]
        have hB := hBstep i hiS
        rw [hAi, hAsucc]
        constructor
        · rintro x ⟨y, hy, rfl⟩
          exact ⟨y, hB.1 hy, rfl⟩
        constructor
        · rw [liftSet, Set.ncard_image_of_injective _ Subtype.val_injective, hB.2.1]
        · exact (induce_liftSet_iso G S (B (i + 1))).connected_iff.mpr hB.2.2
      · have hi_eq : i = Fintype.card S := by omega
        subst i
        have hAcard : A (Fintype.card S) = S := by
          have hle : Fintype.card S ≤ Fintype.card S := le_rfl
          rw [show A (Fintype.card S) = liftSet S (B (Fintype.card S)) by
            dsimp [A]
            rw [if_pos hle]]
          rw [hBcard, liftSet_univ]
        have hAsucc : A (Fintype.card S + 1) = Set.univ := by
          have hnot : ¬Fintype.card S + 1 ≤ Fintype.card S := by omega
          dsimp [A]
          rw [if_neg hnot]
        rw [hAcard, hAsucc]
        constructor
        · exact Set.subset_univ S
        constructor
        · rw [Set.ncard_univ, Nat.card_eq_fintype_card]
          exact hcardα
        · exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hconn

/--
Diestel, Proposition 1.4.1.
The vertices of a finite connected graph can be enumerated so that every
initial induced subgraph is connected.
-/
theorem proposition_1_4_1 {V : Type u} (G : SimpleGraph V) [Fintype V] :
  G.Connected →
    ∃ A : ℕ → Set V,
      A 0 = ∅ ∧
        A (Fintype.card V) = Set.univ ∧
          ∀ i : ℕ, i < Fintype.card V →
            A i ⊆ A (i + 1) ∧
              (A (i + 1)).ncard = i + 1 ∧
                (G.induce (A (i + 1))).Connected :=
  connected_vertex_enumeration G

end Chapter01
end Diestel
