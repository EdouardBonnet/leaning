import Chapter02.tree_exchange_chain_aux
import Mathlib.Combinatorics.Matroid.Circuit

set_option linter.all false

open Set

namespace Diestel
namespace Chapter02

universe u w

namespace MatroidExchange

variable {α : Type u} {M : Matroid α} {B : Set α} {e f a b : α}
variable {ι : Type w}

def FamilyBases (M : Matroid α) (T : ι → Set α) : Prop :=
  ∀ i : ι, M.IsBase (T i)

def BaseExchangeStep (M : Matroid α) (T : ι → Set α) (e f : α) : Prop :=
  ∃ i : ι, M.IsBase (T i) ∧ e ∈ T i ∧ f ∉ T i ∧
    M.IsBase (((T i) ∪ {f}) \ {e})

lemma union_singleton_diff_eq_insert_diff (hfe : f ≠ e) :
    (B ∪ {f}) \ {e} = insert f (B \ {e}) := by
  ext x
  simp only [mem_diff, mem_union, mem_singleton_iff, mem_insert_iff]
  constructor
  · rintro ⟨hxB | hxf, hxe⟩
    · exact Or.inr ⟨hxB, hxe⟩
    · exact Or.inl hxf
  · rintro (hxf | ⟨hxB, hxe⟩)
    · exact ⟨Or.inr hxf, by
        intro hxe
        exact hfe (hxf.symm.trans hxe)⟩
    · exact ⟨Or.inl hxB, hxe⟩

lemma isBase_insert_diff_of_mem_fundCircuit
    (hB : M.IsBase B) (heB : e ∈ B) (hbB : b ∉ B)
    (heFund : e ∈ M.fundCircuit b B) :
    M.IsBase (insert b (B \ {e})) := by
  classical
  have heb : e ≠ b := by
    intro h
    exact hbB (h ▸ heB)
  have hbE : b ∈ M.E := by
    by_contra hbE
    have hfund : M.fundCircuit b B = {b} :=
      Matroid.fundCircuit_eq_of_notMem_ground (M := M) (X := B) hbE
    have : e = b := by
      simpa [hfund] using heFund
    exact heb this
  have hindep : M.Indep (insert b B \ {e}) := by
    rwa [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) hbB] at heFund
  have hEq : insert b B \ {e} = insert b (B \ {e}) := by
    ext x
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hx
      rcases hx.1 with rfl | hxB
      · exact Or.inl rfl
      · exact Or.inr ⟨hxB, hx.2⟩
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨Or.inl rfl, heb.symm⟩
      · exact ⟨Or.inr hx.1, hx.2⟩
  exact hB.exchange_isBase_of_indep (e := e) (f := b) hbB (by
    rwa [← hEq])

/--
Matroid version of the fundamental-cycle persistence used in Diestel's proof.

If `B - e + f` is a base and `e` is not in the fundamental circuit of `b`
with respect to `B`, then the fundamental circuit of `b` is unchanged after
the exchange.
-/
lemma fundCircuit_exchange_eq_of_not_mem
    (hB : M.IsBase B)
    (hBf : M.IsBase (insert f (B \ {e})))
    (hbE : b ∈ M.E) (hbB : b ∉ B) (hbf : b ≠ f)
    (he_not : e ∉ M.fundCircuit b B) :
    M.fundCircuit b (insert f (B \ {e})) = M.fundCircuit b B := by
  classical
  let Bf : Set α := insert f (B \ {e})
  have hC : M.IsCircuit (M.fundCircuit b B) :=
    hB.fundCircuit_isCircuit hbE hbB
  have hCs : M.fundCircuit b B ⊆ insert b Bf := by
    intro x hx
    have hxins : x ∈ insert b B := M.fundCircuit_subset_insert b B hx
    simp only [mem_insert_iff] at hxins ⊢
    rcases hxins with rfl | hxB
    · exact Or.inl rfl
    · exact Or.inr (by
        refine Or.inr ?_
        exact ⟨hxB, by
          intro hxe
          exact he_not (hxe ▸ hx)⟩)
  have hEq : M.fundCircuit b B = M.fundCircuit b Bf :=
    hC.eq_fundCircuit_of_subset hBf.indep hCs
  exact hEq.symm

/--
The corresponding two-exchange commutation theorem for one matroid base.

This is the abstract matroid statement behind the difficult same-tree case in
Lemma 2.4.5: if both `B - e + f` and `B - a + b` are bases, and `e` is not in
the fundamental circuit of `b`, then `B - e + f - a + b` is also a base.
-/
lemma exchange_exchange_isBase_of_not_mem_fundCircuit
    (hB : M.IsBase B)
    (heB : e ∈ B) (hfB : f ∉ B)
    (hBf : M.IsBase (insert f (B \ {e})))
    (haB : a ∈ B) (hane : a ≠ e)
    (hbB : b ∉ B) (hbf : b ≠ f)
    (hBa : M.IsBase (insert b (B \ {a})))
    (he_not : e ∉ M.fundCircuit b B) :
    M.IsBase (insert b ((insert f (B \ {e})) \ {a})) := by
  classical
  have hab : a ≠ b := by
    intro h
    exact hbB (h ▸ haB)
  have hbE : b ∈ M.E := by
    have hbmem : b ∈ insert b (B \ {a}) := mem_insert b _
    exact hBa.subset_ground hbmem
  let Bf : Set α := insert f (B \ {e})
  have hbBf : b ∉ Bf := by
    intro hb
    simp only [Bf, mem_insert_iff, mem_diff, mem_singleton_iff] at hb
    rcases hb with hbf_eq | hb
    · exact hbf hbf_eq
    · exact hbB hb.1
  have haBf : a ∈ Bf := by
    simp [Bf, haB, hane]
  have haFund : a ∈ M.fundCircuit b B := by
    rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) hbB]
    have hEq : insert b B \ {a} = insert b (B \ {a}) := by
      ext x
      simp only [mem_diff, mem_insert_iff, mem_singleton_iff]
      constructor
      · intro hx
        rcases hx.1 with rfl | hxB
        · exact Or.inl rfl
        · exact Or.inr ⟨hxB, hx.2⟩
      · intro hx
        rcases hx with rfl | hx
        · exact ⟨Or.inl rfl, hab.symm⟩
        · exact ⟨Or.inr hx.1, hx.2⟩
    rw [hEq]
    exact hBa.indep
  have hFundEq : M.fundCircuit b Bf = M.fundCircuit b B :=
    fundCircuit_exchange_eq_of_not_mem (M := M) (B := B) (e := e) (f := f)
      (b := b) hB hBf hbE hbB hbf he_not
  have haFundBf : a ∈ M.fundCircuit b Bf := by
    simpa [hFundEq] using haFund
  have hInd : M.Indep (insert b Bf \ {a}) := by
    rwa [hBf.indep.mem_fundCircuit_iff (by rwa [hBf.closure_eq]) hbBf] at haFundBf
  exact hBf.exchange_isBase_of_indep (e := a) (f := b) hbBf (by
    have hEq : insert b (Bf \ {a}) = insert b Bf \ {a} := by
      ext x
      simp only [mem_insert_iff, mem_diff, mem_singleton_iff]
      constructor
      · intro hx
        rcases hx with rfl | hx
        · exact ⟨Or.inl rfl, hab.symm⟩
        · exact ⟨Or.inr hx.1, hx.2⟩
      · intro hx
        rcases hx.1 with rfl | hxBf
        · exact Or.inl rfl
        · exact Or.inr ⟨hxBf, hx.2⟩
    rwa [hEq])

lemma baseExchangeStep_replaceFamily_of_no_shortcut [DecidableEq ι]
    {T : ι → Set α} {i : ι} {e f a b : α}
    (hBi : M.IsBase (T i)) (heBi : e ∈ T i) (hfBi : f ∉ T i)
    (hBf : M.IsBase (((T i) ∪ {f}) \ {e}))
    (hae : a ≠ e) (hbf : b ≠ f)
    (hNoShortcut : ¬ BaseExchangeStep M T e b)
    (hStep : BaseExchangeStep M T a b) :
    BaseExchangeStep M (MultiGraph.replaceFamily T i e f) a b := by
  classical
  rcases hStep with ⟨j, hBj, haBj, hbBj, hBjb⟩
  by_cases hji : j = i
  · subst j
    have hfe : f ≠ e := by
      intro h
      exact hfBi (h ▸ heBi)
    have hba : b ≠ a := by
      intro h
      exact hbBj (h ▸ haBj)
    have hbe : b ≠ e := by
      intro h
      exact hbBj (h ▸ heBi)
    have haf : a ≠ f := by
      intro h
      exact hfBi (h ▸ haBj)
    have hBf_insert : M.IsBase (insert f (T i \ {e})) := by
      rwa [← union_singleton_diff_eq_insert_diff (B := T i) (e := e) (f := f) hfe]
    have hBab_insert : M.IsBase (insert b (T i \ {a})) := by
      rwa [← union_singleton_diff_eq_insert_diff (B := T i) (e := a) (f := b) hba]
    have hnotFund : e ∉ M.fundCircuit b (T i) := by
      intro heFund
      have hShortcutBase_insert :
          M.IsBase (insert b (T i \ {e})) :=
        isBase_insert_diff_of_mem_fundCircuit
          (M := M) (B := T i) (e := e) (b := b) hBi heBi hbBj heFund
      have hShortcutBase : M.IsBase (((T i) ∪ {b}) \ {e}) := by
        rwa [union_singleton_diff_eq_insert_diff (B := T i) (e := e) (f := b) hbe]
      exact hNoShortcut ⟨i, hBi, heBi, hbBj, hShortcutBase⟩
    have hBaseAfter_insert :
        M.IsBase (insert b ((insert f (T i \ {e})) \ {a})) :=
      exchange_exchange_isBase_of_not_mem_fundCircuit
        (M := M) (B := T i) (e := e) (f := f) (a := a) (b := b)
        hBi heBi hfBi hBf_insert haBj hae hbBj hbf hBab_insert hnotFund
    refine ⟨i, ?_, ?_, ?_, ?_⟩
    · simpa [MultiGraph.replaceFamily_self] using hBf
    · simp [MultiGraph.replaceFamily_self, haBj, hae, haf]
    · simp [MultiGraph.replaceFamily_self, hbBj, hbf, hbe]
    · have hBfSet :
          (T i ∪ {f}) \ {e} = insert f (T i \ {e}) :=
        union_singleton_diff_eq_insert_diff (B := T i) (e := e) (f := f) hfe
      have htarget :
          (((T i ∪ {f}) \ {e}) ∪ {b}) \ {a} =
            insert b ((insert f (T i \ {e})) \ {a}) := by
        rw [hBfSet]
        exact union_singleton_diff_eq_insert_diff
          (B := insert f (T i \ {e})) (e := a) (f := b) hba
      rw [MultiGraph.replaceFamily_self, htarget]
      exact hBaseAfter_insert
  · refine ⟨j, ?_, ?_, ?_, ?_⟩
    · simpa [MultiGraph.replaceFamily_ne T hji e f] using hBj
    · simpa [MultiGraph.replaceFamily_ne T hji e f] using haBj
    · simpa [MultiGraph.replaceFamily_ne T hji e f] using hbBj
    · simpa [MultiGraph.replaceFamily_ne T hji e f] using hBjb

end MatroidExchange

end Chapter02
end Diestel
