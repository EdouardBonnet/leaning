import Chapter02.theorem_2_1_1
import Chapter02.dilworth_matching

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Corollary 2.5.2 (Dilworth).
Natural-language statement:
In every finite partially ordered set, the minimum number of chains needed
to cover the set is equal to the maximum size of an antichain.
-/
theorem corollary_2_5_2 (P : Type u) [Fintype P] [DecidableEq P] [PartialOrder P] :
  ChainCover P (maxAntichainCard P) ∧
    ∀ n : ℕ, ChainCover P n → maxAntichainCard P ≤ n := by
  classical
  refine ⟨?_, fun n hcover => DilworthAux.maxAntichainCard_le_of_chainCover P hcover⟩
  let H : SimpleGraph (P ⊕ P) := DilworthMatching.splitOrderGraph P
  have hBip :
      H.IsBipartiteWith (DilworthMatching.leftSide P) (DilworthMatching.rightSide P) := by
    simpa [H] using DilworthMatching.splitOrderGraph_isBipartiteWith P
  have hSides :
      DilworthMatching.leftSide P ∪ DilworthMatching.rightSide P = Set.univ :=
    DilworthMatching.left_union_right P
  obtain ⟨M, hM, hMcard⟩ := DilworthMatching.exists_matchingNumber_subgraph H
  have hchain :
      ChainCover P (Nat.card P - matchingNumber H) := by
    simpa [hMcard] using DilworthMatching.chainCover_of_matching (P := P) (M := M) hM
  have hle :
      Nat.card P - matchingNumber H ≤ maxAntichainCard P := by
    have hKonig :
        (matchingNumber H : ℕ∞) = SimpleGraph.vertexCoverNum H :=
      theorem_2_1_1 H (DilworthMatching.leftSide P) (DilworthMatching.rightSide P)
        hBip hSides
    obtain ⟨C, hCmin, hCcover⟩ := SimpleGraph.vertexCoverNum_exists H
    have hCenc : C.encard = (C.ncard : ℕ∞) := by
      rw [Set.encard_eq_coe_toFinset_card C, Set.ncard_eq_toFinset_card' C]
    have hCnat : C.ncard = matchingNumber H := by
      apply ENat.coe_inj.mp
      calc
        (C.ncard : ℕ∞) = C.encard := hCenc.symm
        _ = SimpleGraph.vertexCoverNum H := hCmin
        _ = (matchingNumber H : ℕ∞) := hKonig.symm
    have hvc :
        Nat.card P - C.ncard ≤ maxAntichainCard P :=
      DilworthMatching.vertexCover_complement_le_maxAntichainCard (P := P) (C := C)
        (by simpa [H] using hCcover)
    simpa [hCnat] using hvc
  exact DilworthAux.chainCover_mono hchain hle

end Chapter02
end Diestel
