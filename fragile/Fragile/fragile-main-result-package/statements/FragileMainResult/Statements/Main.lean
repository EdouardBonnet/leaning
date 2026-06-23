import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Finset

namespace FragileMainResult.Statements.Main

universe u

variable {V : Type u}

def KColorable (m : Nat) (G : SimpleGraph V) : Prop :=
  G.Colorable m

def deleteVertices (G : SimpleGraph V) (S : Finset V) : SimpleGraph {v : V // v ∉ S} :=
  G.induce {v : V | v ∉ S}

def IsVertexSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y : {v : V // v ∉ S}, ¬ (deleteVertices G S).Reachable x y

def ThreeConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Nat.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → ¬ IsVertexSeparator G S

def MFragile (m : Nat) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ThreeConnected H.coe → KColorable (m - 1) H.coe

def HasNoThreeConnectedSubgraph (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ¬ ThreeConnected H.coe

def T3Conditions [DecidableEq V] (m : Nat) (G : SimpleGraph V) : Prop :=
  (∀ {x y : V}, ¬ G.Adj x y →
    ∃ c : G.Coloring (Fin m), c x = c y) ∧
  (∀ {x y : V}, x ≠ y →
    ∃ c : G.Coloring (Fin m), c x ≠ c y) ∧
  (∀ {x y z : V}, x ≠ y → x ≠ z → y ≠ z →
    ∃ c : G.Coloring (Fin m),
      c x ∉ ({c y, c z} : Finset (Fin m))) ∧
  (∀ {x y z : V}, x ≠ y → x ≠ z → y ≠ z →
    ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) →
    ∃ c : G.Coloring (Fin m),
      (({x, y, z} : Finset V).image fun w => c w).card = 2)

axiom theorem3_mfragile {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hfrag : MFragile m G) :
    T3Conditions m G

axiom mfragile_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hfrag : MFragile m G) :
    KColorable m G

axiom theorem2_contra {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hnot : ¬ KColorable m G) :
    ∃ H : G.Subgraph, ThreeConnected H.coe ∧ ¬ KColorable (m - 1) H.coe

axiom theorem2 {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hchi : ((m + 1 : Nat) : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : G.Subgraph, ThreeConnected H.coe ∧ (m : ℕ∞) ≤ H.coe.chromaticNumber

axiom fragile_four_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfragile : HasNoThreeConnectedSubgraph G) :
    KColorable 4 G

end FragileMainResult.Statements.Main
