import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

namespace DilworthAux

lemma antichain_card_le_of_chainCover {P : Type u} [Fintype P] [DecidableEq P]
    [PartialOrder P] {A : Finset P} {n : ℕ}
    (hA : IsAntichainFinset A) (hcover : ChainCover P n) :
    A.card ≤ n := by
  classical
  rcases hcover with ⟨C, hCchain, hCcover⟩
  let f : A → Fin n := fun a => (hCcover a.1).choose
  have hf : Function.Injective f := by
    intro a b hab
    have haC : a.1 ∈ C (f a) := by
      simpa [f] using (hCcover a.1).choose_spec
    have hbC : b.1 ∈ C (f b) := by
      simpa [f] using (hCcover b.1).choose_spec
    have hbC' : b.1 ∈ C (f a) := by
      simpa [f, hab] using hbC
    rcases hCchain (f a) a.1 haC b.1 hbC' with hab_le | hba_le
    · by_cases heq : a.1 = b.1
      · exact Subtype.ext heq
      · exact (hA a.1 a.2 b.1 b.2 heq).1 hab_le |>.elim
    · by_cases heq : a.1 = b.1
      · exact Subtype.ext heq
      · exact (hA a.1 a.2 b.1 b.2 heq).2 hba_le |>.elim
  have hcard : Fintype.card A ≤ Fintype.card (Fin n) :=
    Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe, Fintype.card_fin] using hcard

lemma maxAntichainCard_le_of_chainCover (P : Type u) [Fintype P] [DecidableEq P]
    [PartialOrder P] {n : ℕ} (hcover : ChainCover P n) :
    maxAntichainCard P ≤ n := by
  classical
  rw [maxAntichainCard]
  let p : ℕ → Prop := fun m => ∃ A : Finset P, IsAntichainFinset A ∧ A.card = m
  letI := Classical.decPred p
  change Nat.findGreatest p (Fintype.card P) ≤ n
  have hp0 : p 0 := by
    refine ⟨∅, ?_, by simp⟩
    intro x hx
    simp at hx
  have hpmax : p (Nat.findGreatest p (Fintype.card P)) :=
    Nat.findGreatest_spec (P := p) (m := 0) (n := Fintype.card P) (Nat.zero_le _) hp0
  rcases hpmax with ⟨A, hA, hAcard⟩
  rw [← hAcard]
  exact antichain_card_le_of_chainCover hA hcover

lemma antichain_card_le_maxAntichainCard {P : Type u} [Fintype P] [DecidableEq P]
    [PartialOrder P] {A : Finset P} (hA : IsAntichainFinset A) :
    A.card ≤ maxAntichainCard P := by
  classical
  rw [maxAntichainCard]
  let p : ℕ → Prop := fun m => ∃ A : Finset P, IsAntichainFinset A ∧ A.card = m
  letI := Classical.decPred p
  change A.card ≤ Nat.findGreatest p (Fintype.card P)
  exact Nat.le_findGreatest (P := p) (n := Fintype.card P) A.card_le_univ ⟨A, hA, rfl⟩

lemma chainCover_mono {P : Type u} [Fintype P] [LE P] {m n : ℕ}
    (hcover : ChainCover P m) (hmn : m ≤ n) : ChainCover P n := by
  classical
  rcases hcover with ⟨C, hCchain, hCcover⟩
  refine ⟨fun i : Fin n =>
      if hi : (i : ℕ) < m then C ⟨i, hi⟩ else ∅, ?_, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) < m
    · simpa [hi] using hCchain ⟨i, hi⟩
    · simp [hi, IsChainFinset]
  · intro x
    obtain ⟨i, hi⟩ := hCcover x
    refine ⟨⟨i, lt_of_lt_of_le i.2 hmn⟩, ?_⟩
    simp [i.2, hi]

end DilworthAux

end Chapter02
end Diestel
