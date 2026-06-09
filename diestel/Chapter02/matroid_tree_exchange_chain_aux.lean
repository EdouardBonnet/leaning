import Chapter02.matroid_exchange_aux
import Mathlib.Combinatorics.Matroid.IndepAxioms

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v w

namespace MultiGraph

open MatroidExchange

variable {V : Type u} {E : Type v} {ι : Type w}

lemma baseExchangeStep_of_isExchangeStep {G : MultiGraph V E} {M : Matroid E}
    (hBase : ∀ F : Set E, M.IsBase F ↔ G.IsSpanningTree F)
    {T : ι → Set E} {e f : E}
    (hStep : G.IsExchangeStep T e f) :
    MatroidExchange.BaseExchangeStep M T e f := by
  rcases hStep with ⟨i, hTi, hei, hfi, hRep⟩
  exact ⟨i, (hBase (T i)).2 hTi, hei, hfi, (hBase (((T i) ∪ {f}) \ {e})).2 hRep⟩

lemma isExchangeStep_of_baseExchangeStep {G : MultiGraph V E} {M : Matroid E}
    (hBase : ∀ F : Set E, M.IsBase F ↔ G.IsSpanningTree F)
    {T : ι → Set E} {e f : E}
    (hStep : MatroidExchange.BaseExchangeStep M T e f) :
    G.IsExchangeStep T e f := by
  rcases hStep with ⟨i, hTi, hei, hfi, hRep⟩
  exact ⟨i, (hBase (T i)).1 hTi, hei, hfi, (hBase (((T i) ∪ {f}) \ {e})).1 hRep⟩

lemma exchangeChainTail_replay_of_minimal_matroid [DecidableEq ι]
    {G : MultiGraph V E} {M : Matroid E}
    (hBase : ∀ F : Set E, M.IsBase F ↔ G.IsSpanningTree F)
    {T : ι → Set E} {e f : E} {tail : List E} {i : ι}
    (hchain : IsExchangeChainTail G T e (f :: tail))
    (hmin : ∀ tail' : List E, IsExchangeChainTail G T e tail' →
      (f :: tail).length ≤ tail'.length)
    (hTwo : EdgeInAtLeastTwoTrees T e)
    (hTree : G.IsSpanningTree (T i)) (hei : e ∈ T i) (hfi : f ∉ T i)
    (hTreeReplace : G.IsSpanningTree (((T i) ∪ {f}) \ {e}))
    (hfmem : f ∈ FamilyEdgeSet T) :
    IsExchangeChainTail G (replaceFamily T i e f) f tail := by
  classical
  let T' := replaceFamily T i e f
  have hfirst : G.IsExchangeStep T e f :=
    exchangeChainTail_cons_first_step (G := G) (T := T) (e := e) hchain
  have htail_chain : (f :: tail).IsChain (ExchangeRel G T) :=
    (exchangeChainTail_cons_suffix (G := G) (T := T) (e := e) hchain).1
  have hnew_chain : (f :: tail).IsChain (ExchangeRel G T') := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b l₁ l₂ hdecomp
    have hStepG : G.IsExchangeStep T a b :=
      (List.isChain_iff_forall_rel_of_append_cons_cons.mp htail_chain) hdecomp
    have hchain_decomp : IsExchangeChainTail G T e (l₁ ++ a :: b :: l₂) := by
      simpa [hdecomp] using hchain
    have hmin_decomp :
        ∀ tail' : List E, IsExchangeChainTail G T e tail' →
          (l₁ ++ a :: b :: l₂).length ≤ tail'.length := by
      intro tail' htail'
      simpa [← hdecomp] using hmin tail' htail'
    have hae : a ≠ e := by
      intro hae
      subst a
      exact minimal_exchangeChainTail_no_shortcut_step
        (G := G) (T := T) (e := e) (a := e) (b := b)
        (pref := l₁) (suffix := l₂) hmin_decomp hchain_decomp hStepG
    have hbf : b ≠ f := by
      intro hbf
      subst b
      exact minimal_exchangeChainTail_no_shortcut_step
        (G := G) (T := T) (e := e) (a := a) (b := f)
        (pref := l₁) (suffix := l₂) hmin_decomp hchain_decomp hfirst
    have hNoShortcut : ¬ MatroidExchange.BaseExchangeStep M T e b := by
      intro hShortcut
      have hShortcutG : G.IsExchangeStep T e b :=
        isExchangeStep_of_baseExchangeStep (G := G) (M := M) hBase hShortcut
      exact minimal_exchangeChainTail_no_shortcut_step
        (G := G) (T := T) (e := e) (a := a) (b := b)
        (pref := l₁) (suffix := l₂) hmin_decomp hchain_decomp hShortcutG
    have hStepBase : MatroidExchange.BaseExchangeStep M T a b :=
      baseExchangeStep_of_isExchangeStep (G := G) (M := M) hBase hStepG
    have hStepBase' :
        MatroidExchange.BaseExchangeStep M T' a b :=
      MatroidExchange.baseExchangeStep_replaceFamily_of_no_shortcut
        (M := M) (T := T) (i := i) (e := e) (f := f) (a := a) (b := b)
        ((hBase (T i)).2 hTree) hei hfi
        ((hBase (((T i) ∪ {f}) \ {e})).2 hTreeReplace)
        hae hbf hNoShortcut hStepBase
    exact isExchangeStep_of_baseExchangeStep (G := G) (M := M) hBase hStepBase'
  have hUnionEq : FamilyEdgeSet T' = FamilyEdgeSet T :=
    familyEdgeSet_replaceFamily_eq_of_duplicate (T := T) (i := i)
      (e := e) (f := f) hTwo hei hfmem
  have hlast :
      (f :: tail).getLast (List.cons_ne_nil f tail) =
        (e :: f :: tail).getLast (List.cons_ne_nil e (f :: tail)) := by
    cases tail with
    | nil =>
        simp
    | cons c tail =>
        simp
  refine ⟨hnew_chain, ?_⟩
  intro hmem
  have hmemT : (f :: tail).getLast (List.cons_ne_nil f tail) ∈ FamilyEdgeSet T := by
    simpa [T', hUnionEq] using hmem
  have hmemT' :
      (e :: f :: tail).getLast (List.cons_ne_nil e (f :: tail)) ∈ FamilyEdgeSet T := by
    rw [← hlast]
    exact hmemT
  exact hchain.2 hmemT'

lemma canImprove_of_startsExchangeChain_matroid [DecidableEq ι]
    {G : MultiGraph V E} {M : Matroid E}
    (hBase : ∀ F : Set E, M.IsBase F ↔ G.IsSpanningTree F)
    {T : ι → Set E} {e : E}
    (hFam : G.FamilySpanningTrees T)
    (hStart : G.StartsExchangeChain T e)
    (hTwo : EdgeInAtLeastTwoTrees T e) :
    G.CanImproveTreeFamily T := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ ⦃T : ι → Set E⦄ ⦃e : E⦄ ⦃tail : List E⦄,
      G.FamilySpanningTrees T →
        IsExchangeChainTail G T e tail →
          (∀ tail' : List E, IsExchangeChainTail G T e tail' →
            tail.length ≤ tail'.length) →
            tail.length = n →
              EdgeInAtLeastTwoTrees T e →
                G.CanImproveTreeFamily T
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T e tail hFam hchain hmin hlen hTwo
        cases tail with
        | nil =>
            obtain ⟨i, _j, _hij, hei, _hej⟩ := hTwo
            exact False.elim
              (exchangeChainTail_nil_outside (G := G) (T := T) (e := e)
                hchain ⟨i, hei⟩)
        | cons f rest =>
            have hStep : G.IsExchangeStep T e f :=
              exchangeChainTail_cons_first_step (G := G) (T := T) (e := e) hchain
            by_cases hfNew : f ∉ FamilyEdgeSet T
            · exact canImprove_of_exchangeStep_to_new_edge hFam hStep hTwo hfNew
            · have hfmem : f ∈ FamilyEdgeSet T := not_not.mp hfNew
              rcases hStep with ⟨i, hTree, hei, hfi, hTreeReplace⟩
              let T' := replaceFamily T i e f
              have hFam' : G.FamilySpanningTrees T' :=
                familySpanning_replaceFamily hFam hTreeReplace
              have hEq' : FamilyEdgeSet T' = FamilyEdgeSet T :=
                familyEdgeSet_replaceFamily_eq_of_duplicate (T := T) (i := i)
                  (e := e) (f := f) hTwo hei hfmem
              have hTwo' : EdgeInAtLeastTwoTrees T' f :=
                edgeInAtLeastTwoTrees_replaceFamily_of_mem_family hei hfi hfmem
              have hchain' : IsExchangeChainTail G T' f rest :=
                exchangeChainTail_replay_of_minimal_matroid
                  (G := G) (M := M) (T := T) (e := e) (f := f)
                  (tail := rest) (i := i) hBase hchain hmin hTwo
                  hTree hei hfi hTreeReplace hfmem
              have hStart' : G.StartsExchangeChain T' f :=
                startsExchangeChain_of_chainTail (G := G) (T := T') (e := f) hchain'
              rcases exists_minimal_exchangeChainTail (G := G) (T := T') (e := f) hStart' with
                ⟨tailMin, htailMin, hminMin⟩
              have hle_min : tailMin.length ≤ rest.length :=
                hminMin rest hchain'
              have hlt : tailMin.length < n := by
                simp at hlen
                omega
              have hImp' : G.CanImproveTreeFamily T' :=
                ih tailMin.length hlt
                  (T := T') (e := f) (tail := tailMin)
                  hFam' htailMin hminMin rfl hTwo'
              exact canImprove_of_familyEdgeSet_eq hEq'.symm hImp'
  rcases exists_minimal_exchangeChainTail (G := G) (T := T) (e := e) hStart with
    ⟨tail, htail, hmin⟩
  exact hP tail.length (T := T) (e := e) (tail := tail) hFam htail hmin rfl hTwo

lemma exists_matroid_of_spanningTree_exchange {G : MultiGraph V E} [Finite E]
    (hExists : ∃ F : Set E, G.IsSpanningTree F)
    (hExchange : Matroid.ExchangeProperty (G.IsSpanningTree)) :
    ∃ M : Matroid E, ∀ F : Set E, M.IsBase F ↔ G.IsSpanningTree F := by
  classical
  let M : Matroid E :=
    Matroid.ofIsBaseOfFinite (E := G.edgeSet) (Set.toFinite G.edgeSet)
      (G.IsSpanningTree) hExists hExchange (by
        intro F hF
        exact hF.2.1)
  refine ⟨M, ?_⟩
  intro F
  simp [M]

lemma canImprove_of_startsExchangeChain_spanningTree_exchange [DecidableEq ι]
    {G : MultiGraph V E} [Finite E]
    (hExchange : Matroid.ExchangeProperty (G.IsSpanningTree))
    {T : ι → Set E} {e : E}
    (hFam : G.FamilySpanningTrees T)
    (hStart : G.StartsExchangeChain T e)
    (hTwo : EdgeInAtLeastTwoTrees T e) :
    G.CanImproveTreeFamily T := by
  classical
  have hTwoOrig := hTwo
  obtain ⟨i, _j, _hij, _hei, _hej⟩ := hTwo
  obtain ⟨M, hBase⟩ :=
    exists_matroid_of_spanningTree_exchange (G := G)
      ⟨T i, hFam i⟩ hExchange
  exact canImprove_of_startsExchangeChain_matroid
    (G := G) (M := M) hBase hFam hStart hTwoOrig

end MultiGraph

end Chapter02
end Diestel
