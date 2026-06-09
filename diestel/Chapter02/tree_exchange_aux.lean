import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v w

namespace MultiGraph

variable {V : Type u} {E : Type v} {ι : Type w}

/-- Replace one member of a tree family by adding `f` and deleting `e`. -/
def replaceFamily [DecidableEq ι] (T : ι → Set E) (i : ι) (e f : E) : ι → Set E :=
  fun j => if j = i then ((T j ∪ {f}) \ {e}) else T j

lemma replaceFamily_self [DecidableEq ι] (T : ι → Set E) (i : ι) (e f : E) :
    replaceFamily T i e f i = ((T i ∪ {f}) \ {e}) := by
  simp [replaceFamily]

lemma replaceFamily_ne [DecidableEq ι] (T : ι → Set E) {i j : ι} (hji : j ≠ i)
    (e f : E) :
    replaceFamily T i e f j = T j := by
  simp [replaceFamily, hji]

lemma duplicate_index_ne_of_edgeInAtLeastTwoTrees [DecidableEq ι] {T : ι → Set E}
    {i : ι} {e : E} (hTwo : EdgeInAtLeastTwoTrees T e) (hei : e ∈ T i) :
    ∃ j : ι, j ≠ i ∧ e ∈ T j := by
  rcases hTwo with ⟨j, k, hjk, hej, hek⟩
  by_cases hji : j = i
  · refine ⟨k, ?_, hek⟩
    intro hki
    exact hjk (hji.trans hki.symm)
  · exact ⟨j, hji, hej⟩

lemma familySpanning_replaceFamily [DecidableEq ι] {G : MultiGraph V E}
    {T : ι → Set E} {i : ι} {e f : E}
    (hFam : G.FamilySpanningTrees T)
    (hTree : G.IsSpanningTree (((T i) ∪ {f}) \ {e})) :
    G.FamilySpanningTrees (replaceFamily T i e f) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [replaceFamily_self] using hTree
  · simpa [replaceFamily_ne T hji e f] using hFam j

lemma familyEdgeSet_subset_replaceFamily [DecidableEq ι] {T : ι → Set E}
    {i j : ι} {e f : E} (hji : j ≠ i) (hej : e ∈ T j) :
    FamilyEdgeSet T ⊆ FamilyEdgeSet (replaceFamily T i e f) := by
  intro x hx
  rcases hx with ⟨k, hxk⟩
  by_cases hki : k = i
  · subst k
    by_cases hxe : x = e
    · subst x
      exact ⟨j, by simpa [replaceFamily_ne T hji e f] using hej⟩
    · refine ⟨i, ?_⟩
      simp [replaceFamily_self, hxk, hxe]
  · exact ⟨k, by simpa [replaceFamily_ne T hki e f] using hxk⟩

lemma familyEdgeSet_replaceFamily_subset [DecidableEq ι] {T : ι → Set E}
    {i : ι} {e f : E} (hf : f ∈ FamilyEdgeSet T) :
    FamilyEdgeSet (replaceFamily T i e f) ⊆ FamilyEdgeSet T := by
  intro x hx
  rcases hx with ⟨j, hxj⟩
  by_cases hji : j = i
  · subst j
    have hxj' : x ∈ ((T i ∪ {f}) \ {e}) := by
      simpa [replaceFamily_self] using hxj
    have hxmem : x ∈ T i ∪ {f} := hxj'.1
    rcases hxmem with hxi | hxf
    · exact ⟨i, hxi⟩
    · exact hxf.symm ▸ hf
  · exact ⟨j, by simpa [replaceFamily_ne T hji e f] using hxj⟩

lemma familyEdgeSet_replaceFamily_eq_of_duplicate [DecidableEq ι] {T : ι → Set E}
    {i : ι} {e f : E} (hTwo : EdgeInAtLeastTwoTrees T e) (hei : e ∈ T i)
    (hf : f ∈ FamilyEdgeSet T) :
    FamilyEdgeSet (replaceFamily T i e f) = FamilyEdgeSet T := by
  obtain ⟨j, hji, hej⟩ := duplicate_index_ne_of_edgeInAtLeastTwoTrees hTwo hei
  exact Set.Subset.antisymm (familyEdgeSet_replaceFamily_subset (T := T) (i := i)
    (e := e) (f := f) hf)
    (familyEdgeSet_subset_replaceFamily (T := T) (i := i) (j := j)
      (e := e) (f := f) hji hej)

lemma edgeInAtLeastTwoTrees_replaceFamily_of_mem_family [DecidableEq ι] {T : ι → Set E}
    {i : ι} {e f : E} (hei : e ∈ T i) (hfi : f ∉ T i)
    (hf : f ∈ FamilyEdgeSet T) :
    EdgeInAtLeastTwoTrees (replaceFamily T i e f) f := by
  rcases hf with ⟨j, hfj⟩
  have hji : j ≠ i := by
    intro h
    exact hfi (h ▸ hfj)
  have hfe : f ≠ e := by
    intro h
    subst f
    exact hfi hei
  refine ⟨i, j, ?_, ?_, ?_⟩
  · exact fun hij => hji hij.symm
  · simp [replaceFamily_self, hfe]
  · simpa [replaceFamily_ne T hji e f] using hfj

lemma canImprove_of_familyEdgeSet_eq {G : MultiGraph V E} {T T' : ι → Set E}
    (hEq : FamilyEdgeSet T = FamilyEdgeSet T')
    (hImp : G.CanImproveTreeFamily T') :
    G.CanImproveTreeFamily T := by
  rcases hImp with ⟨S, hS, hss⟩
  refine ⟨S, hS, ?_⟩
  rwa [hEq]

lemma canImprove_of_exchangeStep_to_new_edge [DecidableEq ι] {G : MultiGraph V E}
    {T : ι → Set E} {e f : E}
    (hFam : G.FamilySpanningTrees T) (hStep : G.IsExchangeStep T e f)
    (hTwo : EdgeInAtLeastTwoTrees T e) (hfNew : f ∉ FamilyEdgeSet T) :
    G.CanImproveTreeFamily T := by
  rcases hStep with ⟨i, _hiTree, hei, _hfi, hTreeReplace⟩
  obtain ⟨j, hji, hej⟩ := duplicate_index_ne_of_edgeInAtLeastTwoTrees hTwo hei
  let T' := replaceFamily T i e f
  refine ⟨T', familySpanning_replaceFamily hFam hTreeReplace, ?_⟩
  have hsubset : FamilyEdgeSet T ⊆ FamilyEdgeSet T' :=
    familyEdgeSet_subset_replaceFamily (T := T) (i := i) (j := j) (e := e) (f := f) hji hej
  have hfe : f ≠ e := by
    intro h
    subst f
    exact hfNew ⟨i, hei⟩
  have hfT' : f ∈ FamilyEdgeSet T' := by
    refine ⟨i, ?_⟩
    simp [T', replaceFamily_self, hfe]
  constructor
  · exact hsubset
  · intro hback
    exact hfNew (hback hfT')

lemma startsExchangeChain_first_step {G : MultiGraph V E} {T : ι → Set E} {e : E}
    (hStart : G.StartsExchangeChain T e) (he : e ∈ FamilyEdgeSet T) :
    ∃ f g : E, G.IsExchangeStep T e f ∧
      Relation.ReflTransGen (fun a b => G.IsExchangeStep T a b) f g ∧
        g ∉ FamilyEdgeSet T := by
  rcases hStart with ⟨g, hg, hchain⟩
  rcases Relation.ReflTransGen.cases_head hchain with rfl | ⟨f, hef, hfg⟩
  · exact (hg he).elim
  · exact ⟨f, g, hef, hfg, hg⟩

lemma canImprove_or_first_replacement [DecidableEq ι] {G : MultiGraph V E}
    {T : ι → Set E} {e : E}
    (hFam : G.FamilySpanningTrees T) (hStart : G.StartsExchangeChain T e)
    (hTwo : EdgeInAtLeastTwoTrees T e) :
    G.CanImproveTreeFamily T ∨
      ∃ f g : E, ∃ i : ι,
        G.IsExchangeStep T e f ∧
          Relation.ReflTransGen (fun a b => G.IsExchangeStep T a b) f g ∧
            g ∉ FamilyEdgeSet T ∧ f ∈ FamilyEdgeSet T ∧
              G.FamilySpanningTrees (replaceFamily T i e f) ∧
                FamilyEdgeSet (replaceFamily T i e f) = FamilyEdgeSet T ∧
                  EdgeInAtLeastTwoTrees (replaceFamily T i e f) f := by
  have hTwoOrig := hTwo
  obtain ⟨i₀, _j₀, _hij₀, hei₀, _hej₀⟩ := hTwo
  obtain ⟨f, g, hef, hfg, hg⟩ :=
    startsExchangeChain_first_step (T := T) (e := e) hStart ⟨i₀, hei₀⟩
  by_cases hf : f ∉ FamilyEdgeSet T
  · exact Or.inl (canImprove_of_exchangeStep_to_new_edge hFam hef hTwoOrig hf)
  · rcases hef with ⟨i, _hiTree, hei, hfi, hTreeReplace⟩
    have hfmem : f ∈ FamilyEdgeSet T := by exact not_not.mp hf
    refine Or.inr ⟨f, g, i, ⟨i, hFam i, hei, hfi, hTreeReplace⟩, hfg, hg,
      hfmem, ?_, ?_, ?_⟩
    · exact familySpanning_replaceFamily hFam hTreeReplace
    · exact familyEdgeSet_replaceFamily_eq_of_duplicate hTwoOrig hei hfmem
    · exact edgeInAtLeastTwoTrees_replaceFamily_of_mem_family hei hfi hfmem

lemma exchangeStep_replaceFamily_of_successor_mem [DecidableEq ι] {G : MultiGraph V E}
    {T : ι → Set E} {i : ι} {e f g : E}
    (hfi : f ∉ T i) (hStep : G.IsExchangeStep T f g) :
    G.IsExchangeStep (replaceFamily T i e f) f g := by
  rcases hStep with ⟨j, hTree, hfj, hgj, hTreeReplace⟩
  have hji : j ≠ i := by
    intro h
    exact hfi (h ▸ hfj)
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · simpa [replaceFamily_ne T hji e f] using hTree
  · simpa [replaceFamily_ne T hji e f] using hfj
  · simpa [replaceFamily_ne T hji e f] using hgj
  · simpa [replaceFamily_ne T hji e f] using hTreeReplace

lemma canImprove_of_two_exchangeSteps_to_new_edge [DecidableEq ι] {G : MultiGraph V E}
    {T : ι → Set E} {e f g : E}
    (hFam : G.FamilySpanningTrees T) (hef : G.IsExchangeStep T e f)
    (hfg : G.IsExchangeStep T f g) (hTwo : EdgeInAtLeastTwoTrees T e)
    (hgNew : g ∉ FamilyEdgeSet T) :
    G.CanImproveTreeFamily T := by
  by_cases hfNew : f ∉ FamilyEdgeSet T
  · exact canImprove_of_exchangeStep_to_new_edge hFam hef hTwo hfNew
  · have hfmem : f ∈ FamilyEdgeSet T := not_not.mp hfNew
    rcases hef with ⟨i, _hTree, hei, hfi, hTreeReplace⟩
    let T' := replaceFamily T i e f
    have hFam' : G.FamilySpanningTrees T' :=
      familySpanning_replaceFamily hFam hTreeReplace
    have hEq' : FamilyEdgeSet T' = FamilyEdgeSet T :=
      familyEdgeSet_replaceFamily_eq_of_duplicate hTwo hei hfmem
    have hTwo' : EdgeInAtLeastTwoTrees T' f :=
      edgeInAtLeastTwoTrees_replaceFamily_of_mem_family hei hfi hfmem
    have hfg' : G.IsExchangeStep T' f g :=
      exchangeStep_replaceFamily_of_successor_mem (T := T) (i := i) (e := e)
        (f := f) (g := g) hfi hfg
    have hgNew' : g ∉ FamilyEdgeSet T' := by
      intro hg
      exact hgNew (hEq' ▸ hg)
    exact canImprove_of_familyEdgeSet_eq hEq'.symm
      (canImprove_of_exchangeStep_to_new_edge hFam' hfg' hTwo' hgNew')

end MultiGraph

end Chapter02
end Diestel
