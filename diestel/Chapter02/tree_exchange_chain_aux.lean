import Chapter02.tree_exchange_aux
import Mathlib.Data.List.Chain

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v w

namespace MultiGraph

variable {V : Type u} {E : Type v} {ι : Type w}

/-- The exchange-step relation associated with a fixed tree family. -/
abbrev ExchangeRel (G : MultiGraph V E) (T : ι → Set E) : E → E → Prop :=
  fun e f => G.IsExchangeStep T e f

/--
A concrete exchange chain starting at `e`, represented by the tail of a non-empty list
`e :: tail`.  The last edge of the list lies outside the current family union.
-/
def IsExchangeChainTail (G : MultiGraph V E) (T : ι → Set E)
    (e : E) (tail : List E) : Prop :=
  (e :: tail).IsChain (ExchangeRel G T) ∧
    (e :: tail).getLast (List.cons_ne_nil e tail) ∉ FamilyEdgeSet T

lemma startsExchangeChain_iff_exists_chainTail {G : MultiGraph V E}
    {T : ι → Set E} {e : E} :
    G.StartsExchangeChain T e ↔
      ∃ tail : List E, IsExchangeChainTail G T e tail := by
  constructor
  · rintro ⟨f, hf, hchain⟩
    rcases List.exists_isChain_cons_of_relationReflTransGen hchain with
      ⟨tail, htail, hlast⟩
    refine ⟨tail, htail, ?_⟩
    simpa [hlast] using hf
  · rintro ⟨tail, htail, hlast⟩
    refine ⟨(e :: tail).getLast (List.cons_ne_nil e tail), hlast, ?_⟩
    exact List.relationReflTransGen_of_exists_isChain_cons tail htail rfl

lemma exists_chainTail_of_startsExchangeChain {G : MultiGraph V E}
    {T : ι → Set E} {e : E} (h : G.StartsExchangeChain T e) :
    ∃ tail : List E, IsExchangeChainTail G T e tail :=
  startsExchangeChain_iff_exists_chainTail.mp h

lemma startsExchangeChain_of_chainTail {G : MultiGraph V E}
    {T : ι → Set E} {e : E} {tail : List E}
    (h : IsExchangeChainTail G T e tail) :
    G.StartsExchangeChain T e :=
  startsExchangeChain_iff_exists_chainTail.mpr ⟨tail, h⟩

lemma exchangeChainTail_nil_outside {G : MultiGraph V E}
    {T : ι → Set E} {e : E}
    (h : IsExchangeChainTail G T e []) :
    e ∉ FamilyEdgeSet T := by
  simpa [IsExchangeChainTail] using h.2

lemma exchangeChainTail_tail_ne_nil_of_mem_family {G : MultiGraph V E}
    {T : ι → Set E} {e : E} {tail : List E}
    (h : IsExchangeChainTail G T e tail) (he : e ∈ FamilyEdgeSet T) :
    tail ≠ [] := by
  intro htail
  subst tail
  exact exchangeChainTail_nil_outside (G := G) (T := T) (e := e) h he

lemma exchangeChainTail_cons_first_step {G : MultiGraph V E}
    {T : ι → Set E} {e f : E} {tail : List E}
    (h : IsExchangeChainTail G T e (f :: tail)) :
    G.IsExchangeStep T e f := by
  have hchain := h.1
  rw [List.isChain_cons_cons] at hchain
  exact hchain.1

lemma exchangeChainTail_cons_suffix {G : MultiGraph V E}
    {T : ι → Set E} {e f : E} {tail : List E}
    (h : IsExchangeChainTail G T e (f :: tail)) :
    IsExchangeChainTail G T f tail := by
  constructor
  · have hchain := h.1
    rw [List.isChain_cons_cons] at hchain
    exact hchain.2
  · simpa [IsExchangeChainTail] using h.2

lemma startsExchangeChain_cons_suffix {G : MultiGraph V E}
    {T : ι → Set E} {e f : E} {tail : List E}
    (h : IsExchangeChainTail G T e (f :: tail)) :
    G.StartsExchangeChain T f :=
  startsExchangeChain_of_chainTail
    (exchangeChainTail_cons_suffix (G := G) (T := T) (e := e) h)

/-- There is an exchange chain tail of length `n`. -/
def HasExchangeChainTailLength (G : MultiGraph V E) (T : ι → Set E)
    (e : E) (n : ℕ) : Prop :=
  ∃ tail : List E, IsExchangeChainTail G T e tail ∧ tail.length = n

lemma exists_chainTailLength_of_startsExchangeChain {G : MultiGraph V E}
    {T : ι → Set E} {e : E} (h : G.StartsExchangeChain T e) :
    ∃ n : ℕ, HasExchangeChainTailLength G T e n := by
  rcases exists_chainTail_of_startsExchangeChain h with ⟨tail, htail⟩
  exact ⟨tail.length, tail, htail, rfl⟩

/--
The shortest concrete exchange chain promised by `StartsExchangeChain`.
This is the formal counterpart of Diestel's "choose a chain of minimum length".
-/
lemma exists_minimal_exchangeChainTail {G : MultiGraph V E}
    {T : ι → Set E} {e : E} (h : G.StartsExchangeChain T e) :
    ∃ tail : List E, IsExchangeChainTail G T e tail ∧
      ∀ tail' : List E, IsExchangeChainTail G T e tail' →
        tail.length ≤ tail'.length := by
  classical
  let p : ℕ → Prop := HasExchangeChainTailLength G T e
  have hp : ∃ n : ℕ, p n := exists_chainTailLength_of_startsExchangeChain h
  rcases Nat.find_spec hp with ⟨tail, htail, hlen⟩
  refine ⟨tail, htail, ?_⟩
  intro tail' htail'
  have hp' : p tail'.length := ⟨tail', htail', rfl⟩
  have hmin : Nat.find hp ≤ tail'.length := Nat.find_min' (H := hp) hp'
  simpa [hlen] using hmin

lemma minimal_exchangeChainTail_no_shortcut {G : MultiGraph V E}
    {T : ι → Set E} {e : E} {tail : List E}
    (hmin : ∀ tail' : List E, IsExchangeChainTail G T e tail' →
      tail.length ≤ tail'.length)
    (hchain : IsExchangeChainTail G T e tail)
    {a b : E} (hprefix : Relation.ReflTransGen (ExchangeRel G T) e a)
    (hshortcut : G.IsExchangeStep T a b)
    (hsuffix : Relation.ReflTransGen (ExchangeRel G T) b
      ((e :: tail).getLast (List.cons_ne_nil e tail))) :
    tail.length ≤
      (Classical.choose
        (List.exists_isChain_cons_of_relationReflTransGen
          ((Relation.ReflTransGen.trans hprefix
            (Relation.ReflTransGen.single hshortcut)).trans hsuffix))).length := by
  classical
  let hnew :
      Relation.ReflTransGen (ExchangeRel G T) e
        ((e :: tail).getLast (List.cons_ne_nil e tail)) :=
    (Relation.ReflTransGen.trans hprefix
      (Relation.ReflTransGen.single hshortcut)).trans hsuffix
  let newTail :=
    Classical.choose (List.exists_isChain_cons_of_relationReflTransGen hnew)
  have hnewSpec :=
    Classical.choose_spec (List.exists_isChain_cons_of_relationReflTransGen hnew)
  have hnewChain : (e :: newTail).IsChain (ExchangeRel G T) := hnewSpec.1
  have hnewLast :
      (e :: newTail).getLast (List.cons_ne_nil e newTail) =
        (e :: tail).getLast (List.cons_ne_nil e tail) := hnewSpec.2
  have houtside :
      (e :: newTail).getLast (List.cons_ne_nil e newTail) ∉ FamilyEdgeSet T := by
    simpa [hnewLast] using hchain.2
  exact hmin newTail ⟨hnewChain, houtside⟩

lemma minimal_exchangeChainTail_no_shortcut_step {G : MultiGraph V E}
    {T : ι → Set E} {e a b : E} {pref suffix : List E}
    (hmin : ∀ tail' : List E, IsExchangeChainTail G T e tail' →
      (pref ++ a :: b :: suffix).length ≤ tail'.length)
    (hchain : IsExchangeChainTail G T e (pref ++ a :: b :: suffix))
    (hshortcut : G.IsExchangeStep T e b) :
    False := by
  classical
  let newTail : List E := b :: suffix
  have hsuffix_chain : (b :: suffix).IsChain (ExchangeRel G T) := by
    have h := hchain.1
    rw [List.isChain_cons_append_cons_cons] at h
    exact h.2.2
  have hnew_chain : (e :: newTail).IsChain (ExchangeRel G T) := by
    simp only [newTail]
    rw [List.isChain_cons_cons]
    exact ⟨hshortcut, hsuffix_chain⟩
  have hlast :
      (e :: newTail).getLast (List.cons_ne_nil e newTail) =
        (e :: (pref ++ a :: b :: suffix)).getLast
          (List.cons_ne_nil e (pref ++ a :: b :: suffix)) := by
    simp only [newTail]
    cases suffix with
    | nil =>
        simp
    | cons c suffix =>
        simp
  have hnew_tail : IsExchangeChainTail G T e newTail := by
    exact ⟨hnew_chain, by simpa [hlast] using hchain.2⟩
  have hle := hmin newTail hnew_tail
  have hlt : newTail.length < (pref ++ a :: b :: suffix).length := by
    simp [newTail]
    omega
  exact (Nat.not_lt_of_ge hle) hlt

lemma canImprove_or_minimal_first_replacement [DecidableEq ι]
    {G : MultiGraph V E} {T : ι → Set E} {e : E}
    (hFam : G.FamilySpanningTrees T)
    (hStart : G.StartsExchangeChain T e)
    (hTwo : EdgeInAtLeastTwoTrees T e) :
    G.CanImproveTreeFamily T ∨
      ∃ f : E, ∃ tail : List E, ∃ i : ι,
        IsExchangeChainTail G T e (f :: tail) ∧
          (∀ tail' : List E, IsExchangeChainTail G T e tail' →
            (f :: tail).length ≤ tail'.length) ∧
          f ∈ FamilyEdgeSet T ∧
            G.FamilySpanningTrees (replaceFamily T i e f) ∧
              FamilyEdgeSet (replaceFamily T i e f) = FamilyEdgeSet T ∧
                EdgeInAtLeastTwoTrees (replaceFamily T i e f) f := by
  classical
  rcases exists_minimal_exchangeChainTail (G := G) (T := T) (e := e) hStart with
    ⟨tail, htail, hmin⟩
  have hTwoOrig := hTwo
  obtain ⟨i₀, _j₀, _hij₀, hei₀, _hej₀⟩ := hTwo
  have heFam : e ∈ FamilyEdgeSet T := ⟨i₀, hei₀⟩
  have htail_ne : tail ≠ [] :=
    exchangeChainTail_tail_ne_nil_of_mem_family (G := G) (T := T) (e := e)
      htail heFam
  cases tail with
  | nil =>
      exact False.elim (htail_ne rfl)
  | cons f tail =>
      have hStep : G.IsExchangeStep T e f :=
        exchangeChainTail_cons_first_step (G := G) (T := T) (e := e) htail
      by_cases hfNew : f ∉ FamilyEdgeSet T
      · exact Or.inl (canImprove_of_exchangeStep_to_new_edge hFam hStep hTwoOrig hfNew)
      · have hfmem : f ∈ FamilyEdgeSet T := not_not.mp hfNew
        rcases hStep with ⟨i, _hiTree, hei, hfi, hTreeReplace⟩
        refine Or.inr ⟨f, tail, i, htail, ?_, hfmem, ?_, ?_, ?_⟩
        · intro tail' htail'
          exact hmin tail' htail'
        · exact familySpanning_replaceFamily hFam hTreeReplace
        · exact familyEdgeSet_replaceFamily_eq_of_duplicate hTwoOrig hei hfmem
        · exact edgeInAtLeastTwoTrees_replaceFamily_of_mem_family hei hfi hfmem

/--
The inductive core of Diestel's Lemma 2.4.5.

The hypothesis `hReplay` is exactly the graph-theoretic persistence assertion
proved in the text from shortest exchange chains and unchanged fundamental
cycles: after the first replacement, if the new edge was already in the family
union, the remaining suffix is still an exchange chain for the modified family.
-/
lemma canImprove_of_chainTail_replay [DecidableEq ι]
    {G : MultiGraph V E}
    (hReplay :
      ∀ ⦃T : ι → Set E⦄ ⦃e f : E⦄ ⦃tail : List E⦄ ⦃i : ι⦄,
        G.FamilySpanningTrees T →
          IsExchangeChainTail G T e (f :: tail) →
            G.IsSpanningTree (T i) →
              e ∈ T i →
                f ∉ T i →
                  G.IsSpanningTree (((T i) ∪ {f}) \ {e}) →
                    f ∈ FamilyEdgeSet T →
                      IsExchangeChainTail G (replaceFamily T i e f) f tail) :
    ∀ ⦃T : ι → Set E⦄ ⦃e : E⦄ ⦃tail : List E⦄,
      G.FamilySpanningTrees T →
        IsExchangeChainTail G T e tail →
          EdgeInAtLeastTwoTrees T e →
            G.CanImproveTreeFamily T := by
  intro T e tail
  induction tail generalizing T e with
  | nil =>
      intro _hFam hchain hTwo
      obtain ⟨i, _j, _hij, hei, _hej⟩ := hTwo
      exact False.elim
        (exchangeChainTail_nil_outside (G := G) (T := T) (e := e) hchain ⟨i, hei⟩)
  | cons f tail ih =>
      intro hFam hchain hTwo
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
          familyEdgeSet_replaceFamily_eq_of_duplicate hTwo hei hfmem
        have hTwo' : EdgeInAtLeastTwoTrees T' f :=
          edgeInAtLeastTwoTrees_replaceFamily_of_mem_family hei hfi hfmem
        have hchain' : IsExchangeChainTail G T' f tail :=
          hReplay hFam hchain hTree hei hfi hTreeReplace hfmem
        exact canImprove_of_familyEdgeSet_eq hEq'.symm
          (ih (T := T') (e := f) hFam' hchain' hTwo')

/--
The `StartsExchangeChain` form of the replay reduction.

This is the exact outer shape of Lemma 2.4.5, except that the
fundamental-cycle persistence step from Diestel's minimum-chain proof is kept
as the explicit hypothesis `hReplay`.
-/
lemma canImprove_of_startsExchangeChain_replay [DecidableEq ι]
    {G : MultiGraph V E}
    (hReplay :
      ∀ ⦃T : ι → Set E⦄ ⦃e f : E⦄ ⦃tail : List E⦄ ⦃i : ι⦄,
        G.FamilySpanningTrees T →
          IsExchangeChainTail G T e (f :: tail) →
            G.IsSpanningTree (T i) →
              e ∈ T i →
                f ∉ T i →
                  G.IsSpanningTree (((T i) ∪ {f}) \ {e}) →
                    f ∈ FamilyEdgeSet T →
                      IsExchangeChainTail G (replaceFamily T i e f) f tail)
    {T : ι → Set E} {e : E}
    (hFam : G.FamilySpanningTrees T)
    (hStart : G.StartsExchangeChain T e)
    (hTwo : EdgeInAtLeastTwoTrees T e) :
    G.CanImproveTreeFamily T := by
  rcases exists_chainTail_of_startsExchangeChain (G := G) (T := T) (e := e) hStart with
    ⟨tail, htail⟩
  exact canImprove_of_chainTail_replay (G := G) hReplay hFam htail hTwo

end MultiGraph

end Chapter02
end Diestel
