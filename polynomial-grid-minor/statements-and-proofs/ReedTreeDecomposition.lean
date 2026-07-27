import «statements-and-proofs».BalancedSeparation
import «statements-and-proofs».TreewidthContract
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Tactic

/-!
# Recursive tree decompositions from balanced separations

This file contains the recursive decomposition step used in Reed's
factor-constant route from balanced separators to bounded treewidth.
-/

namespace SimpleGraph

universe u

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ReedTreeDecomposition

/-- Join two trees by one edge between specified vertices. -/
def joinTrees {A B : Type*} (TA : _root_.SimpleGraph A)
    (TB : _root_.SimpleGraph B) (a : A) (b : B) :
    _root_.SimpleGraph (A ⊕ B) :=
  (TA ⊕g TB) ⊔ _root_.SimpleGraph.edge
    (Sum.inl a : A ⊕ B) (Sum.inr b : A ⊕ B)

private abbrev sumInlHom {A B : Type*} (TA : _root_.SimpleGraph A)
    (TB : _root_.SimpleGraph B) : TA →g TA ⊕g TB where
  toFun := Sum.inl
  map_rel' := by simpa

private abbrev sumInrHom {A B : Type*} (TA : _root_.SimpleGraph A)
    (TB : _root_.SimpleGraph B) : TB →g TA ⊕g TB where
  toFun := Sum.inr
  map_rel' := by simpa

private theorem exists_leftWalk {A B : Type*} {TA : _root_.SimpleGraph A}
    {TB : _root_.SimpleGraph B} {s x : A ⊕ B}
    (p : (TA ⊕g TB).Walk s x) : ∀ (a : A) (hs : s = Sum.inl a),
    ∃ a' : A, ∃ q : TA.Walk a a', ∃ hx : x = Sum.inl a',
      q.map (sumInlHom TA TB) = p.copy hs hx := by
  induction p with
  | nil =>
      intro a ha
      cases ha
      exact ⟨a, .nil, rfl, rfl⟩
  | @cons u v w hadj tail ih =>
      intro a ha
      subst u
      cases v with
      | inl v =>
          rcases ih v rfl with ⟨a', q, hw, hq⟩
          refine ⟨a', .cons (by simpa using hadj) q, hw, ?_⟩
          cases hw
          cases hq
          rfl
      | inr v => simp at hadj

private theorem exists_rightWalk {A B : Type*} {TA : _root_.SimpleGraph A}
    {TB : _root_.SimpleGraph B} {s x : A ⊕ B}
    (p : (TA ⊕g TB).Walk s x) : ∀ (b : B) (hs : s = Sum.inr b),
    ∃ b' : B, ∃ q : TB.Walk b b', ∃ hx : x = Sum.inr b',
      q.map (sumInrHom TA TB) = p.copy hs hx := by
  induction p with
  | nil =>
      intro b hb
      cases hb
      exact ⟨b, .nil, rfl, rfl⟩
  | @cons u v w hadj tail ih =>
      intro b hb
      subst u
      cases v with
      | inl v => simp at hadj
      | inr v =>
          rcases ih v rfl with ⟨b', q, hw, hq⟩
          refine ⟨b', .cons (by simpa using hadj) q, hw, ?_⟩
          cases hw
          cases hq
          rfl

private theorem sum_isAcyclic {A B : Type*}
    {TA : _root_.SimpleGraph A} {TB : _root_.SimpleGraph B}
    (hA : TA.IsAcyclic) (hB : TB.IsAcyclic) : (TA ⊕g TB).IsAcyclic := by
  intro v p hp
  cases v with
  | inl v =>
      rcases exists_leftWalk p v rfl with ⟨v', q, hv', hq⟩
      have hvv : v' = v := Sum.inl_injective hv'.symm
      subst v'
      apply hA q
      apply (Walk.map_isCycle_iff_of_injective
        (f := sumInlHom TA TB) Sum.inl_injective).mp
      rw [hq]
      simpa using hp
  | inr v =>
      rcases exists_rightWalk p v rfl with ⟨v', q, hv', hq⟩
      have hvv : v' = v := Sum.inr_injective hv'.symm
      subst v'
      apply hB q
      apply (Walk.map_isCycle_iff_of_injective
        (f := sumInrHom TA TB) Sum.inr_injective).mp
      rw [hq]
      simpa using hp

theorem joinTrees_isTree {A B : Type*} [Finite A] [Finite B]
    {TA : _root_.SimpleGraph A} {TB : _root_.SimpleGraph B}
    (hA : TA.IsTree) (hB : TB.IsTree) (a : A) (b : B) :
    (joinTrees TA TB a b).IsTree := by
  refine ⟨?_, ?_⟩
  · exact hA.connected.sum_sup_edge (v := a) (w := b) hB.connected
  · apply (sum_isAcyclic hA.isAcyclic hB.isAcyclic).sup_edge_of_not_reachable
    intro hab
    rcases hab with ⟨p⟩
    rcases exists_leftWalk p a rfl with ⟨a', q, hbad, _⟩
    simp at hbad

/-- A tree decomposition of the subgraph carried by a finite region.  The
walk formulation of the running-intersection property makes recursive gluing
independent of subtype coercions. -/
structure RegionDecomposition (G : _root_.SimpleGraph V) (C : Finset V) where
  Node : Type
  [nodeFintype : Fintype Node]
  [nodeDecidableEq : DecidableEq Node]
  tree : _root_.SimpleGraph Node
  isTree : tree.IsTree
  root : Node
  bag : Node → Finset V
  bag_subset : ∀ i, bag i ⊆ C
  vertex_mem_bag : ∀ {v : V}, v ∈ C → ∃ i, v ∈ bag i
  edge_mem_bag : ∀ {u v : V}, G.Adj u v → u ∈ C → v ∈ C →
    ∃ i, u ∈ bag i ∧ v ∈ bag i
  bag_walk : ∀ {v : V}, v ∈ C → ∀ {i j : Node},
    v ∈ bag i → v ∈ bag j →
    ∃ p : tree.Walk i j, ∀ n ∈ p.support, v ∈ bag n

namespace RegionDecomposition

variable {G : _root_.SimpleGraph V} {C : Finset V}

/-- The one-bag decomposition of a region. -/
noncomputable def oneBag (G : _root_.SimpleGraph V) (C : Finset V) :
    RegionDecomposition G C where
  Node := Unit
  tree := ⊥
  isTree := _root_.SimpleGraph.IsTree.of_subsingleton
  root := ()
  bag := fun _ => C
  bag_subset := fun _ => subset_rfl
  vertex_mem_bag := by intro v hv; exact ⟨(), hv⟩
  edge_mem_bag := by intro u v _ hu hv; exact ⟨(), hu, hv⟩
  bag_walk := by
    intro v hv i j hi hj
    have hij : i = j := Subsingleton.elim _ _
    subst j
    exact ⟨.nil, by simpa⟩

/-- The rooted two-child tree used by recursive gluing. -/
def attachTree (D₁ : RegionDecomposition G C) {C₂ : Finset V}
    (D₂ : RegionDecomposition G C₂) :
    _root_.SimpleGraph ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  joinTrees (joinTrees (⊥ : _root_.SimpleGraph Unit) D₁.tree () D₁.root)
    D₂.tree (Sum.inl ()) D₂.root

theorem attachTree_isTree (D₁ : RegionDecomposition G C) {C₂ : Finset V}
    (D₂ : RegionDecomposition G C₂) : (attachTree D₁ D₂).IsTree := by
  letI := D₁.nodeFintype
  letI := D₂.nodeFintype
  apply joinTrees_isTree
  · exact joinTrees_isTree _root_.SimpleGraph.IsTree.of_subsingleton D₁.isTree () D₁.root
  · exact D₂.isTree

private abbrev leftNode {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₁.Node → ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  fun i => Sum.inl (Sum.inr i)

private abbrev rightNode {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₂.Node → ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  Sum.inr

private abbrev centerNode {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    ((Unit ⊕ D₁.Node) ⊕ D₂.Node) :=
  Sum.inl (Sum.inl ())

private def leftHom {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₁.tree →g attachTree D₁ D₂ where
  toFun := leftNode D₁ D₂
  map_rel' := by
    intro i j hij
    simp [attachTree, joinTrees, hij]

private def rightHom {C₁ C₂ : Finset V}
    (D₁ : RegionDecomposition G C₁) (D₂ : RegionDecomposition G C₂) :
    D₂.tree →g attachTree D₁ D₂ where
  toFun := rightNode D₁ D₂
  map_rel' := by
    intro i j hij
    simp [attachTree, joinTrees, hij]

end RegionDecomposition

end ReedTreeDecomposition

end SimpleGraph
