import Chapter02.stable_matching_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

open StableMatchingAux

/--
Diestel, Theorem 2.1.4 (Gale-Shapley).
For every set of preferences in a finite bipartite graph, there is a stable
matching.
-/
theorem theorem_2_1_4 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (A B : Set V) (P : Preferences G) :
  G.IsBipartiteWith A B →
    A ∪ B = Set.univ →
      ∃ M : G.Subgraph, StableMatching G P M := by
  classical
  intro hAB hcover
  letI : DecidableEq V := Classical.decEq V
  let good : ℕ → Prop :=
    fun n => ∃ S : Finset G.edgeSet, ValidState G A B P S ∧ S.card = n
  letI : DecidablePred good := Classical.decPred good
  let bound : ℕ := Fintype.card G.edgeSet
  have hgood0 : good 0 := by
    refine ⟨∅, validState_empty G, ?_⟩
    simp
  have hgoodMax : good (Nat.findGreatest good bound) :=
    Nat.findGreatest_spec (P := good) (n := bound) (Nat.zero_le bound) hgood0
  rcases hgoodMax with ⟨S, hValid, hSmax⟩
  have hTerm : TerminalState G A B P S := by
    by_contra hnot
    rcases validState_extend_of_not_terminal G hAB hValid hnot with
      ⟨T, hTvalid, hcardlt⟩
    have hTbound : T.card ≤ bound := by
      simpa [bound] using Finset.card_le_univ T
    have hgoodT : good T.card := ⟨T, hTvalid, rfl⟩
    have hfind_lt : Nat.findGreatest good bound < T.card := by
      calc
        Nat.findGreatest good bound = S.card := hSmax.symm
        _ < T.card := hcardlt
    exact (Nat.findGreatest_is_greatest (P := good) (n := bound) hfind_lt hTbound) hgoodT
  exact ⟨heldSubgraph G B P S, terminalState_stable G hAB hcover hValid hTerm⟩

end Chapter02
end Diestel
