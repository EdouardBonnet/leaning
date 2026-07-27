import «statements-and-proofs».ChekuriChuzhoySection5Selection
import «statements-and-proofs».ChekuriChuzhoySection5TerminalSkeleton

/-!
# Deterministic group selection for terminal skeletons

Theorem 5.12 stores edge groups as a `Finpartition`, while the deterministic
simultaneous-selection theorem uses a group-label function.  This module gives
the exact adapter and packages the one-per-group selection used in both phases
of the Section 5 assembly.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5TerminalSkeleton

universe u

open Finset
open ChekuriChuzhoySection5Selection

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {terminals : Finset V}

namespace TerminalPathSkeleton

/-- The finite type of groups in a terminal skeleton. -/
abbrev GroupIndex (S : TerminalPathSkeleton G terminals) :=
  {U : Finset S.graph.Edge // U ∈ S.groups.parts}

/-- The unique partition part containing an abstract edge copy. -/
noncomputable def groupOf (S : TerminalPathSkeleton G terminals)
    (e : S.graph.Edge) : S.GroupIndex := by
  classical
  exact ⟨S.groups.part e, S.groups.part_mem.mpr (by simp)⟩

theorem mem_groupOf (S : TerminalPathSkeleton G terminals)
    (e : S.graph.Edge) : e ∈ (S.groupOf e).1 := by
  classical
  exact S.groups.mem_part (by simp)

theorem groupOf_eq_iff_mem (S : TerminalPathSkeleton G terminals)
    (e : S.graph.Edge) (U : S.GroupIndex) :
    S.groupOf e = U ↔ e ∈ U.1 := by
  classical
  constructor
  · intro h
    rw [← h]
    exact S.mem_groupOf e
  · intro he
    apply Subtype.ext
    exact S.groups.part_eq_of_mem U.2 he

/-- A fiber of `groupOf` is exactly its corresponding partition part. -/
theorem filter_groupOf_eq (S : TerminalPathSkeleton G terminals)
    (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U) = U.1 := by
  classical
  ext e
  simp [S.groupOf_eq_iff_mem e U]

theorem image_groupOf_univ (S : TerminalPathSkeleton G terminals) :
    (Finset.univ.image S.groupOf) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro U
  rcases S.groups.nonempty_of_mem_parts U.2 with ⟨e, he⟩
  exact Finset.mem_image.mpr
    ⟨e, Finset.mem_univ e, (S.groupOf_eq_iff_mem e U).2 he⟩

/-- Bounded skeleton groups become the exact fiber bound required by the
deterministic selection theorem. -/
theorem groupFiber_card_le
    (S : TerminalPathSkeleton G terminals) {maxGroupSize : ℕ}
    (hsize : S.GroupSizeAtMost maxGroupSize) (U : S.GroupIndex) :
    (Finset.univ.filter fun e : S.graph.Edge => S.groupOf e = U).card ≤
      maxGroupSize := by
  rw [S.filter_groupOf_eq U]
  exact hsize U.1 U.2

/-- Exact group-label transversals are precisely one-per-part selections in
the skeleton's native representation. -/
theorem isGroupTransversal_of_exact
    (S : TerminalPathSkeleton G terminals) {selected : Finset S.graph.Edge}
    (hselected : IsExactGroupTransversal Finset.univ S.groupOf selected) :
    S.IsGroupTransversal selected := by
  classical
  intro U hU
  let g : S.GroupIndex := ⟨U, hU⟩
  have hg : g ∈ (Finset.univ : Finset S.GroupIndex).image id := by simp
  have hgImage : g ∈ (Finset.univ : Finset S.graph.Edge).image S.groupOf := by
    rw [S.image_groupOf_univ]
    simp
  rcases hselected.existsUnique_mem_group hgImage with ⟨e, he, hunique⟩
  have heU : e ∈ U := (S.groupOf_eq_iff_mem e g).1 he.2
  have hsubset : selected ∩ U ⊆ {e} := by
    intro f hf
    have hfSelected := (Finset.mem_inter.mp hf).1
    have hfU := (Finset.mem_inter.mp hf).2
    have hfg : S.groupOf f = g := (S.groupOf_eq_iff_mem f g).2 hfU
    have hfe : f = e := hunique f ⟨hfSelected, hfg⟩
    simpa [hfe]
  have heInter : e ∈ selected ∩ U := Finset.mem_inter.mpr ⟨he.1, heU⟩
  exact Finset.card_eq_one.mpr ⟨e, Finset.Subset.antisymm hsubset (by
    intro f hf
    have hfe : f = e := Finset.mem_singleton.mp hf
    simpa [hfe] using heInter)⟩

/-- Deterministically select one edge copy from every skeleton group while
retaining `q` copies in every requested bundle. -/
theorem exists_groupTransversal_retaining_bundles
    (S : TerminalPathSkeleton G terminals)
    (bundles : Finset (Finset S.graph.Edge))
    (maxGroupSize r q : ℕ)
    (hmax : 0 < maxGroupSize)
    (hbundles : ∀ B ∈ bundles, B ⊆ Finset.univ)
    (hcount : bundles.card ≤ r)
    (hsize : S.GroupSizeAtMost maxGroupSize)
    (hbundleSize : ∀ B ∈ bundles,
      maxGroupSize * (r * q) ≤ B.card) :
    ∃ selected : Finset S.graph.Edge,
      S.IsGroupTransversal selected ∧
        ∀ B ∈ bundles, q ≤ (selected ∩ B).card := by
  classical
  rcases exists_exactGroupTransversal_of_bounded_groups
      (Finset.univ : Finset S.graph.Edge) S.groupOf bundles
      maxGroupSize r q hmax hbundles hcount
      (fun U _hU => S.groupFiber_card_le hsize U) hbundleSize with
    ⟨selected, hexact, hretain⟩
  exact ⟨selected, S.isGroupTransversal_of_exact hexact, hretain⟩

end TerminalPathSkeleton
end ChekuriChuzhoySection5TerminalSkeleton
end SimpleGraph
