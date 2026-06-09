import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma not_edgeInAtLeastTwoTrees_fin_zero (T : Fin 0 → Set E) (e : E) :
    ¬ EdgeInAtLeastTwoTrees T e := by
  rintro ⟨i, _j, _hij, _hei, _hej⟩
  exact Fin.elim0 i

lemma not_edgeInAtLeastTwoTrees_fin_one (T : Fin 1 → Set E) (e : E) :
    ¬ EdgeInAtLeastTwoTrees T e := by
  rintro ⟨i, j, hij, _hei, _hej⟩
  exact hij (Subsingleton.elim i j)

/-- The `k = 0` specialization of Diestel, Lemma 2.4.5. -/
theorem lemma_2_4_5_k_zero {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (T : Fin 0 → Set E) (e : E) :
    G.Loopless →
      G.FamilySpanningTrees T →
        G.StartsExchangeChain T e →
          EdgeInAtLeastTwoTrees T e →
            G.CanImproveTreeFamily T := by
  intro _hloopless _hFam _hStart hTwo
  exact False.elim ((not_edgeInAtLeastTwoTrees_fin_zero T e) hTwo)

/-- The `k = 1` specialization of Diestel, Lemma 2.4.5. -/
theorem lemma_2_4_5_k_one {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (T : Fin 1 → Set E) (e : E) :
    G.Loopless →
      G.FamilySpanningTrees T →
        G.StartsExchangeChain T e →
          EdgeInAtLeastTwoTrees T e →
            G.CanImproveTreeFamily T := by
  intro _hloopless _hFam _hStart hTwo
  exact False.elim ((not_edgeInAtLeastTwoTrees_fin_one T e) hTwo)

end MultiGraph

end Chapter02
end Diestel
