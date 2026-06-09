import Chapter01.definitions_ch1
import Mathlib.Data.Set.Finite.Basic

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

private def cutSymmSide {V : Type u} (A B : Set V) : Set V :=
  (A \ B) ∪ (B \ A)

private lemma mk_mem_cut_edges_iff {V : Type u} (G : SimpleGraph V) (A : Set V)
    {x y : V} {he : s(x, y) ∈ G.edgeSet} :
    (⟨s(x, y), he⟩ : G.edgeSet) ∈ cut_edges G A ↔
      (x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A) := by
  constructor
  · rintro ⟨a, ha, b, hb, hxy⟩
    rcases Sym2.eq_iff.mp hxy with h | h
    · exact Or.inl ⟨by simpa [h.1] using ha, by simpa [h.2] using hb⟩
    · exact Or.inr ⟨by simpa [h.2] using ha, by simpa [h.1] using hb⟩
  · intro h
    rcases h with h | h
    · exact ⟨x, h.1, y, h.2, rfl⟩
    · exact ⟨y, h.1, x, h.2, by
        change s(x, y) = s(y, x)
        rw [Sym2.eq_swap]⟩

private lemma cut_edges_symmSide {V : Type u} (G : SimpleGraph V) (A B : Set V) :
    cut_edges G (cutSymmSide A B) =
      (cut_edges G A \ cut_edges G B) ∪ (cut_edges G B \ cut_edges G A) := by
  classical
  ext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y =>
      by_cases hxA : x ∈ A <;>
      by_cases hyA : y ∈ A <;>
      by_cases hxB : x ∈ B <;>
      by_cases hyB : y ∈ B <;>
      simp [cutSymmSide, mk_mem_cut_edges_iff, hxA, hyA, hxB, hyB]

private lemma cut_edges_sdiff_of_subset {V : Type u} (G : SimpleGraph V)
    {A B : Set V} (hsub : cut_edges G B ⊆ cut_edges G A) :
    cut_edges G (cutSymmSide A B) = cut_edges G A \ cut_edges G B := by
  rw [cut_edges_symmSide]
  ext e
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim (h.2 (hsub h.1))
  · intro h
    exact Or.inl h

private lemma cut_edges_nonempty_sides {V : Type u} (G : SimpleGraph V) (A : Set V)
    (h : (cut_edges G A).Nonempty) : A.Nonempty ∧ Aᶜ.Nonempty := by
  rcases h with ⟨e, x, hx, y, hy, _hxy⟩
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

private lemma isCut_sdiff_of_subset {V : Type u} (G : SimpleGraph V)
    {F D : Set G.edgeSet} (hF : IsCut G F) (hD : IsCut G D)
    (hsub : D ⊆ F) (hne : (F \ D).Nonempty) : IsCut G (F \ D) := by
  rcases hF with ⟨A, _hA, _hAc, rfl⟩
  rcases hD with ⟨B, _hB, _hBc, rfl⟩
  let C := cutSymmSide A B
  have hCeq : cut_edges G C = cut_edges G A \ cut_edges G B := by
    exact cut_edges_sdiff_of_subset G hsub
  have hCne : (cut_edges G C).Nonempty := by
    rw [hCeq]
    exact hne
  have hsides := cut_edges_nonempty_sides G C hCne
  exact ⟨C, hsides.1, hsides.2, hCeq.symm⟩

private theorem cut_decomposition_aux {V : Type u} (G : SimpleGraph V) [Fintype V] :
    ∀ n : ℕ, ∀ F : Set G.edgeSet, F.ncard = n → IsCut G F →
      ∃ bonds : Set (Set G.edgeSet),
        (∀ B ∈ bonds, IsBond G B) ∧
          (∀ B₁ ∈ bonds, ∀ B₂ ∈ bonds, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
            F = {e | ∃ B ∈ bonds, e ∈ B} := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro F hFn hFcut
      by_cases hFempty : F = ∅
      · refine ⟨∅, ?_, ?_, ?_⟩
        · intro B hB
          exact False.elim hB
        · intro B hB
          exact False.elim hB
        · ext e
          simp [hFempty]
      · have hFne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hFempty
        by_cases hbond : IsBond G F
        · refine ⟨{F}, ?_, ?_, ?_⟩
          · intro B hB
            simpa using hB ▸ hbond
          · intro B₁ hB₁ B₂ hB₂ hne
            have hB₁eq : B₁ = F := by simpa using hB₁
            have hB₂eq : B₂ = F := by simpa using hB₂
            exact False.elim (hne (hB₁eq.trans hB₂eq.symm))
          · ext e
            constructor
            · intro he
              exact ⟨F, by simp, he⟩
            · rintro ⟨B, hB, heB⟩
              have hBeq : B = F := by simpa using hB
              simpa [hBeq] using heB
        · have hnotmin :
              ¬ ∀ D : Set G.edgeSet, IsCut G D → D.Nonempty → D ⊆ F → F ⊆ D := by
            intro hmin
            exact hbond ⟨hFcut, hFne, by
              intro D hDcut hDne hDF
              exact hmin D hDcut hDne hDF⟩
          obtain ⟨D, hDnot⟩ := not_forall.mp hnotmin
          obtain ⟨hDcut, hDnot⟩ := Classical.not_imp.mp hDnot
          obtain ⟨hDne, hDnot⟩ := Classical.not_imp.mp hDnot
          obtain ⟨hDF, hFnotD⟩ := Classical.not_imp.mp hDnot
          have hDssub : D ⊂ F := ⟨hDF, hFnotD⟩
          have hDn_lt : D.ncard < n := by
            rw [← hFn]
            exact Set.ncard_lt_ncard hDssub
          have hrem_ne : (F \ D).Nonempty := Set.diff_nonempty.mpr hFnotD
          have hrem_cut : IsCut G (F \ D) :=
            isCut_sdiff_of_subset G hFcut hDcut hDF hrem_ne
          have hrem_sub : F \ D ⊂ F := by
            refine ⟨?_, ?_⟩
            · intro e he
              exact he.1
            · intro hFsub
              rcases hDne with ⟨e, heD⟩
              have heF : e ∈ F := hDF heD
              have heRem : e ∈ F \ D := hFsub heF
              exact heRem.2 heD
          have hrem_lt : (F \ D).ncard < n := by
            rw [← hFn]
            exact Set.ncard_lt_ncard hrem_sub
          obtain ⟨bondsD, hbD, hdisD, hUD⟩ :=
            ih D.ncard hDn_lt D rfl hDcut
          obtain ⟨bondsR, hbR, hdisR, hUR⟩ :=
            ih (F \ D).ncard hrem_lt (F \ D) rfl hrem_cut
          refine ⟨bondsD ∪ bondsR, ?_, ?_, ?_⟩
          · intro B hB
            rcases hB with hB | hB
            · exact hbD B hB
            · exact hbR B hB
          · intro B₁ hB₁ B₂ hB₂ hne
            rcases hB₁ with hB₁ | hB₁ <;> rcases hB₂ with hB₂ | hB₂
            · exact hdisD B₁ hB₁ B₂ hB₂ hne
            · refine Set.disjoint_left.mpr ?_
              intro e he₁ he₂
              have heD : e ∈ D := by
                rw [hUD]
                exact ⟨B₁, hB₁, he₁⟩
              have heR : e ∈ F \ D := by
                rw [hUR]
                exact ⟨B₂, hB₂, he₂⟩
              exact heR.2 heD
            · refine Set.disjoint_left.mpr ?_
              intro e he₁ he₂
              have heR : e ∈ F \ D := by
                rw [hUR]
                exact ⟨B₁, hB₁, he₁⟩
              have heD : e ∈ D := by
                rw [hUD]
                exact ⟨B₂, hB₂, he₂⟩
              exact heR.2 heD
            · exact hdisR B₁ hB₁ B₂ hB₂ hne
          · ext e
            constructor
            · intro heF
              by_cases heD : e ∈ D
              · rw [hUD] at heD
                rcases heD with ⟨B, hB, heB⟩
                exact ⟨B, Or.inl hB, heB⟩
              · have heR : e ∈ F \ D := ⟨heF, heD⟩
                rw [hUR] at heR
                rcases heR with ⟨B, hB, heB⟩
                exact ⟨B, Or.inr hB, heB⟩
            · rintro ⟨B, hB, heB⟩
              rcases hB with hB | hB
              · have heD : e ∈ D := by
                  rw [hUD]
                  exact ⟨B, hB, heB⟩
                exact hDF heD
              · have heR : e ∈ F \ D := by
                  rw [hUR]
                  exact ⟨B, hB, heB⟩
                exact heR.1

/--
Diestel, Lemma 1.9.3.
Every cut is a disjoint union of bonds.
-/
theorem lemma_1_9_3 {V : Type u} (G : SimpleGraph V) [Fintype V] (F : Set G.edgeSet) :
    IsCut G F →
      ∃ bonds : Set (Set G.edgeSet),
        (∀ B ∈ bonds, IsBond G B) ∧
          (∀ B₁ ∈ bonds, ∀ B₂ ∈ bonds, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
            F = {e | ∃ B ∈ bonds, e ∈ B} := by
  intro hF
  exact cut_decomposition_aux G F.ncard F rfl hF

end Chapter01
end Diestel
