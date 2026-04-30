import TwinWidth.Contraction.Trigraph

/-!
# Twin-width of finite simple graphs

Twin-width is defined using contraction sequences of trigraph states.  A state
keeps the original vertex type fixed and tracks the current contracted vertices
as bags.  The width of a sequence is the maximum red degree of any bag occurring
in any intermediate state.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The red degree of a current bag in a trigraph state. -/
noncomputable def redDegree {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A : Finset V) : ℕ :=
  T.redDegree A

/-- The initial trigraph state for a graph has singleton bags, black edges
exactly where the graph has edges, and no red edges. -/
def IsInitialState {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (T : TrigraphState V) : Prop :=
  T.bags = TrigraphState.singletonBags V ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags →
      T.blackAdj A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b) ∧
    (∀ ⦃A B⦄, A ∈ T.bags → B ∈ T.bags → ¬ T.redAdj A B)

/-- A final trigraph state has at most one bag.

For nonempty graphs this means the usual single contracted bag.  The `≤ 1`
convention also treats the empty graph as already fully contracted.
-/
def IsFinalState {V : Type*} (T : TrigraphState V) : Prop :=
  T.bags.card ≤ 1

/-- The bag of previous-state vertices represented by a next-state bag after
contracting `A` and `B`. -/
def contractionPreimages {V : Type*} [DecidableEq V]
    (A B X : Finset V) : Finset (Finset V) :=
  if X = A ∪ B then {A, B} else {X}

/-- Red adjacency after contracting `A` and `B`.

For the merged bag, red edges are inherited red edges or disagreements between
the two old black adjacencies.  Pairs of bags not involving the merged bag keep
their old red status.
-/
def contractedRed {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.redAdj A Y ∨ T.redAdj B Y ∨ T.blackAdj A Y ≠ T.blackAdj B Y
  else if Y = A ∪ B then
    T.redAdj X A ∨ T.redAdj X B ∨ T.blackAdj X A ≠ T.blackAdj X B
  else
    T.redAdj X Y

/-- Black adjacency after contracting `A` and `B`.

For the merged bag, a black edge to another bag remains only when both old
adjacencies were black and no red edge is created.  Other pairs are unchanged.
-/
def contractedBlack {V : Type*} [DecidableEq V]
    (T : TrigraphState V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    T.blackAdj A Y ∧ T.blackAdj B Y ∧ ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    T.blackAdj X A ∧ T.blackAdj X B ∧ ¬ contractedRed T A B X Y
  else
    T.blackAdj X Y

/-- `U` is obtained from `T` by contracting two distinct bags. -/
def IsContractionStep {V : Type*} [DecidableEq V]
    (T U : TrigraphState V) : Prop :=
  ∃ A ∈ T.bags, ∃ B ∈ T.bags, A ≠ B ∧
    U.bags = insert (A ∪ B) ((T.bags.erase A).erase B) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      U.redAdj X Y ↔ contractedRed T A B X Y) ∧
    (∀ ⦃X Y⦄, X ∈ U.bags → Y ∈ U.bags →
      U.blackAdj X Y ↔ contractedBlack T A B X Y)

/-- A concrete contraction sequence of width at most `d`. -/
structure ContractionSequence {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) where
  /-- Number of contraction steps. -/
  stepCount : ℕ
  /-- The trigraph state at each time. -/
  state : ℕ → TrigraphState V
  /-- The first state is the singleton-bag encoding of `G`. -/
  starts : IsInitialState G (state 0)
  /-- The last state consists of one bag. -/
  ends : IsFinalState (state stepCount)
  /-- Consecutive states are related by one bag contraction. -/
  step_contracts : ∀ i, i < stepCount → IsContractionStep (state i) (state (i + 1))
  /-- Every bag in every state has red degree at most `d`. -/
  redDegree_le : ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ (state i).bags → redDegree (state i) A ≤ d

/-- `G` has twin-width at most `d` if it has a contraction sequence whose red
degree never exceeds `d`. -/
def HasTwinWidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (ContractionSequence G d)

/-- The twin-width of a graph is the least width admitting a contraction
sequence.  The fallback branch is unreachable once existence of contraction
sequences is proved for all finite graphs; keeping it here makes the definition
total without using axioms. -/
noncomputable def twinWidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact if h : ∃ d, HasTwinWidthAtMost G d then Nat.find h else 0

theorem hasTwinWidthAtMost_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d e : ℕ}
    (h : HasTwinWidthAtMost G d) (hde : d ≤ e) :
    HasTwinWidthAtMost G e := by
  rcases h with ⟨S⟩
  refine ⟨(?_ : ContractionSequence G e)⟩
  exact ContractionSequence.mk S.stepCount S.state S.starts S.ends S.step_contracts
    (fun i hi A hA => le_trans (S.redDegree_le i hi hA) hde)

theorem twinWidth_le_of_hasTwinWidthAtMost {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {d : ℕ}
    (h : HasTwinWidthAtMost G d) :
    twinWidth G ≤ d := by
  classical
  have hex : ∃ e, HasTwinWidthAtMost G e := ⟨d, h⟩
  rw [twinWidth, dif_pos hex]
  exact Nat.find_min' hex h

theorem hasTwinWidthAtMost_twinWidth {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (h : ∃ d, HasTwinWidthAtMost G d) :
    HasTwinWidthAtMost G (twinWidth G) := by
  classical
  rw [twinWidth, dif_pos h]
  exact Nat.find_spec h

end SimpleGraph
end TwinWidth
