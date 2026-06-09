import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fintype.Card

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u v

private theorem tree_isContained_of_minDegree_aux {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ {W : Type v} [Fintype W] (T : SimpleGraph W),
      T.IsTree → Fintype.card W - 1 < G.minDegree → SimpleGraph.IsContained T G := by
  classical
  refine fun {W} _ =>
    Fintype.induction_subsingleton_or_nontrivial
      (P := fun W [Fintype W] =>
        ∀ T : SimpleGraph W,
          T.IsTree → Fintype.card W - 1 < G.minDegree → SimpleGraph.IsContained T G)
      W ?base ?step
  · intro W _ hsub T hT hmin
    have hW_nonempty : Nonempty W := hT.connected.nonempty
    have hW_card : Fintype.card W = 1 := by
      haveI : Unique W := {
        default := Classical.choice hW_nonempty
        uniq := fun w => Subsingleton.elim w (Classical.choice hW_nonempty) }
      exact Fintype.card_unique
    have hG_pos : 0 < G.minDegree := by
      rw [hW_card] at hmin
      exact hmin
    have hV_nonempty : Nonempty V := by
      by_contra hV
      haveI : IsEmpty V := not_nonempty_iff.mp hV
      have hzero : G.minDegree = 0 := SimpleGraph.minDegree_of_isEmpty G
      omega
    let v : V := Classical.choice hV_nonempty
    refine ⟨⟨{
      toFun := fun _ => v
      map_rel' := ?_
    }, ?_⟩⟩
    · intro a b hab
      have hab_eq : a = b := Subsingleton.elim a b
      subst b
      exact (T.loopless.irrefl a hab).elim
    · intro a b _hab
      exact Subsingleton.elim a b
  · intro W _ hnontriv ih T hT hmin
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    obtain ⟨x, hxdeg⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨y, hxy, hy_unique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxdeg
    let S : Set W := {x}ᶜ
    let yS : S := ⟨y, by
      change y ∈ ({x}ᶜ : Set W)
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hxy.ne'⟩
    have hcardS : Fintype.card S = Fintype.card W - 1 := by
      dsimp [S]
      rw [Fintype.card_compl_set ({x} : Set W)]
      simp
    have hcardS_lt : Fintype.card S < Fintype.card W := by
      rw [hcardS]
      exact Nat.sub_one_lt (Nat.ne_of_gt (Fintype.card_pos_iff.mpr hT.connected.nonempty))
    have hT' : (T.induce S).IsTree := by
      refine ⟨?_, ?_⟩
      · exact hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg
      · exact hT.isAcyclic.induce S
    have hmin' : Fintype.card S - 1 < G.minDegree := by
      rw [hcardS]
      omega
    obtain ⟨f⟩ := ih S hcardS_lt (T.induce S) hT' hmin'
    have hcardS_lt_min : Fintype.card S < G.minDegree := by
      rw [hcardS]
      exact hmin
    have hcardS_lt_degree : Fintype.card S < G.degree (f yS) :=
      hcardS_lt_min.trans_le (G.minDegree_le_degree (f yS))
    obtain ⟨z, hz_adj, hz_not_mem⟩ :
        ∃ z : V, G.Adj (f yS) z ∧ z ∉ Set.range (fun s : S => f s) := by
      by_contra hnone
      have hsubset :
          G.neighborFinset (f yS) ⊆
            (Finset.univ.image (fun s : S => f s) : Finset V) := by
        intro z hz
        have hz_adj' : G.Adj (f yS) z :=
          (SimpleGraph.mem_neighborFinset G (f yS) z).mp hz
        have hz_range : z ∈ Set.range (fun s : S => f s) := by
          by_contra hz_not
          exact hnone ⟨z, hz_adj', hz_not⟩
        rcases hz_range with ⟨s, rfl⟩
        exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
      have hdeg_le : G.degree (f yS) ≤
          (Finset.univ.image (fun s : S => f s) : Finset V).card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card hsubset
      have himage_le :
          (Finset.univ.image (fun s : S => f s) : Finset V).card ≤ Fintype.card S :=
        Finset.card_image_le
      exact (Nat.not_lt_of_ge (hdeg_le.trans himage_le)) hcardS_lt_degree
    let φ : W → V := fun w =>
      if h : w = x then z else f ⟨w, by
        change w ∈ ({x}ᶜ : Set W)
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact h⟩
    refine ⟨⟨{
      toFun := φ
      map_rel' := ?_
    }, ?_⟩⟩
    · intro a b hab
      by_cases hax : a = x
      · subst a
        by_cases hbx : b = x
        · subst b
          exact (T.loopless.irrefl x hab).elim
        · have hb_eq_y : b = y := hy_unique b hab
          subst b
          have hy_ne_x : y ≠ x := hxy.ne'
          have hyS_eq : (⟨y, by
              change y ∈ ({x}ᶜ : Set W)
              rw [Set.mem_compl_iff, Set.mem_singleton_iff]
              exact hy_ne_x⟩ : S) = yS := by
            rfl
          change G.Adj (φ x) (φ y)
          rw [show φ x = z by simp [φ],
            show φ y = f yS by
              dsimp [φ]
              rw [dif_neg hy_ne_x, hyS_eq]]
          exact hz_adj.symm
      · by_cases hbx : b = x
        · subst b
          have ha_eq_y : a = y := hy_unique a hab.symm
          subst a
          have hy_ne_x : y ≠ x := hxy.ne'
          have hyS_eq : (⟨y, by
              change y ∈ ({x}ᶜ : Set W)
              rw [Set.mem_compl_iff, Set.mem_singleton_iff]
              exact hy_ne_x⟩ : S) = yS := by
            rfl
          change G.Adj (φ y) (φ x)
          rw [show φ y = f yS by
              dsimp [φ]
              rw [dif_neg hy_ne_x, hyS_eq],
            show φ x = z by simp [φ]]
          exact hz_adj
        · have haS : a ∈ S := by
            change a ∈ ({x}ᶜ : Set W)
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact hax
          have hbS : b ∈ S := by
            change b ∈ ({x}ᶜ : Set W)
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact hbx
          have h_ind : (T.induce S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ := hab
          change G.Adj (φ a) (φ b)
          rw [show φ a = f ⟨a, haS⟩ by
              dsimp [φ]
              rw [dif_neg hax],
            show φ b = f ⟨b, hbS⟩ by
              dsimp [φ]
              rw [dif_neg hbx]]
          exact f.toHom.map_adj h_ind
    · intro a b hab
      by_cases hax : a = x
      · subst a
        by_cases hbx : b = x
        · exact hbx.symm
        · have hbS : b ∈ S := by
            change b ∈ ({x}ᶜ : Set W)
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact hbx
          have hφb : φ b = f ⟨b, hbS⟩ := by
            dsimp [φ]
            rw [dif_neg hbx]
          have hz_range : z ∈ Set.range (fun s : S => f s) := by
            refine ⟨⟨b, hbS⟩, ?_⟩
            calc
              (fun s : S => f s) ⟨b, hbS⟩ = f ⟨b, hbS⟩ := rfl
              _ = φ b := hφb.symm
              _ = φ x := hab.symm
              _ = z := by simp [φ]
          exact (hz_not_mem hz_range).elim
      · by_cases hbx : b = x
        · subst b
          have haS : a ∈ S := by
            change a ∈ ({x}ᶜ : Set W)
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact hax
          have hφa : φ a = f ⟨a, haS⟩ := by
            dsimp [φ]
            rw [dif_neg hax]
          have hz_range : z ∈ Set.range (fun s : S => f s) := by
            refine ⟨⟨a, haS⟩, ?_⟩
            calc
              (fun s : S => f s) ⟨a, haS⟩ = f ⟨a, haS⟩ := rfl
              _ = φ a := hφa.symm
              _ = φ x := hab
              _ = z := by simp [φ]
          exact (hz_not_mem hz_range).elim
        · have haS : a ∈ S := by
            change a ∈ ({x}ᶜ : Set W)
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact hax
          have hbS : b ∈ S := by
            change b ∈ ({x}ᶜ : Set W)
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact hbx
          have hφa : φ a = f ⟨a, haS⟩ := by
            dsimp [φ]
            rw [dif_neg hax]
          have hφb : φ b = f ⟨b, hbS⟩ := by
            dsimp [φ]
            rw [dif_neg hbx]
          have hf_eq : f ⟨a, haS⟩ = f ⟨b, hbS⟩ := by
            rw [← hφa, ← hφb]
            exact hab
          exact congrArg Subtype.val (f.injective hf_eq)

/--
Diestel, Corollary 1.5.3.
If `T` is a tree and `δ(G) > |T| - 1`, then `G` contains a copy of `T`.
-/
theorem corollary_1_5_3 {V : Type u} {W : Type v}
    (T : SimpleGraph W) (G : SimpleGraph V)
    [Fintype W] [Fintype V] [DecidableRel G.Adj] :
  T.IsTree → Fintype.card W - 1 < G.minDegree → SimpleGraph.IsContained T G :=
  tree_isContained_of_minDegree_aux G T

end Chapter01
end Diestel
