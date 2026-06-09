import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

variable {V : Type u} {E : Type v}

lemma edgeDisjointFamily_comp_finCastLE {k l : ℕ} (hkl : l ≤ k)
    {T : Fin k → Set E} (hdisj : EdgeDisjointFamily T) :
    EdgeDisjointFamily (fun i : Fin l => T (Fin.castLE hkl i)) := by
  intro i j hij
  apply hdisj
  intro h
  exact hij (Fin.ext (congrArg (fun x : Fin k => x.1) h))

lemma hasKEdgeDisjointSpanningTrees_mono_down {G : MultiGraph V E}
    {k l : ℕ} (hkl : l ≤ k) :
    G.HasKEdgeDisjointSpanningTrees k →
      G.HasKEdgeDisjointSpanningTrees l := by
  intro hpack
  rcases hpack with ⟨T, hTrees, hdisj⟩
  refine ⟨fun i : Fin l => T (Fin.castLE hkl i), ?_, ?_⟩
  · intro i
    exact hTrees (Fin.castLE hkl i)
  · exact edgeDisjointFamily_comp_finCastLE hkl hdisj

lemma hasKEdgeDisjointSpanningTreesOn_mono_down {G : MultiGraph V E}
    {U : Set V} {k l : ℕ} (hkl : l ≤ k) :
    G.HasKEdgeDisjointSpanningTreesOn U k →
      G.HasKEdgeDisjointSpanningTreesOn U l := by
  intro hpack
  rcases hpack with ⟨T, hTrees, hdisj⟩
  refine ⟨fun i : Fin l => T (Fin.castLE hkl i), ?_, ?_⟩
  · intro i
    exact hTrees (Fin.castLE hkl i)
  · exact edgeDisjointFamily_comp_finCastLE hkl hdisj

lemma hasKDisjointCycles_mono_down {G : MultiGraph V E}
    {k l : ℕ} (hkl : l ≤ k) :
    G.HasKDisjointCycles k → G.HasKDisjointCycles l := by
  intro hcycles
  rcases hcycles with ⟨C, hdisj⟩
  refine ⟨fun i : Fin l => C (Fin.castLE hkl i), ?_⟩
  intro i j hij
  apply hdisj
  intro h
  exact hij (Fin.ext (congrArg (fun x : Fin k => x.1) h))

lemma canCoverEdgesByAtMostKTrees_mono {G : MultiGraph V E}
    {k l : ℕ} (hkl : k ≤ l) :
    G.CanCoverEdgesByAtMostKTrees k →
      G.CanCoverEdgesByAtMostKTrees l := by
  rintro ⟨n, hn, T, hForest, hCovered⟩
  exact ⟨n, hn.trans hkl, T, hForest, hCovered⟩

lemma canCoverEdgesByAtMostKSpanningTrees_mono {G : MultiGraph V E}
    {k l : ℕ} (hkl : k ≤ l) :
    G.CanCoverEdgesByAtMostKSpanningTrees k →
      G.CanCoverEdgesByAtMostKSpanningTrees l := by
  rintro ⟨n, hn, T, hTrees, hCovered⟩
  exact ⟨n, hn.trans hkl, T, hTrees, hCovered⟩

end MultiGraph

end Chapter02
end Diestel
