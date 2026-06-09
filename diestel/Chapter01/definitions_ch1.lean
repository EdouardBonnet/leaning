import Mathlib.Algebra.Module.Pi
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Defs

set_option linter.all false

open scoped BigOperators
open Finset

universe u v

namespace Diestel
namespace Chapter01

variable {V : Type u} {W : Type v}

/-- Diestel's order `|G|`, represented by the cardinality of the vertex type. -/
abbrev order (G : SimpleGraph V) [Fintype V] : ℕ :=
  Fintype.card V

/-- Diestel's edge count `‖G‖`, represented by Mathlib's finite edge set. -/
abbrev edge_count (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℕ :=
  #G.edgeFinset

/-- A graph of order at most one. -/
def IsTrivial (G : SimpleGraph V) [Fintype V] : Prop :=
  Fintype.card V ≤ 1

/-- A cubic graph is a 3-regular graph. -/
abbrev IsCubic (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  G.IsRegularOfDegree 3

/-- The neighbours of a vertex set `U`, excluding vertices already in `U`. -/
def neighbors_of_set (G : SimpleGraph V) (U : Set V) : Set V :=
  {v | v ∉ U ∧ ∃ u ∈ U, G.Adj u v}

/-- The set of edges with one end in `X` and one end in `Y`. -/
def edge_set_between (G : SimpleGraph V) (X Y : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y)}

/-- Diestel's average degree `d(G)`, as a rational number. -/
noncomputable def average_degree (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℚ :=
  (∑ v : V, (G.degree v : ℚ)) / Fintype.card V

/-- Diestel's edge/vertex ratio `ε(G) = |E(G)| / |V(G)|`, as a rational number. -/
noncomputable def edge_vertex_ratio (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℚ :=
  (#G.edgeFinset : ℚ) / Fintype.card V

/-- The inner vertices of a walk, excluding its two endpoints. -/
def walk_inner_vertices {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Set V :=
  {x | x ∈ p.support ∧ x ≠ a ∧ x ≠ b}

/--
An `A`-`B` path: a path that meets `A` exactly in its first vertex and
meets `B` exactly in its last vertex.
-/
def IsABPath (G : SimpleGraph V) {a b : V} (p : G.Walk a b) (A B : Set V) : Prop :=
  p.IsPath ∧ a ∈ A ∧ b ∈ B ∧
    (∀ ⦃x : V⦄, x ∈ p.support → x ∈ A → x = a) ∧
    (∀ ⦃x : V⦄, x ∈ p.support → x ∈ B → x = b)

/--
A non-trivial path whose ends, but no inner vertices, lie in the set `A`.
This is Diestel's `A`-path.
-/
def IsSetPath (G : SimpleGraph V) {a b : V} (p : G.Walk a b) (A : Set V) : Prop :=
  p.IsPath ∧ 0 < p.length ∧ a ∈ A ∧ b ∈ A ∧
    ∀ ⦃x : V⦄, x ∈ walk_inner_vertices p → x ∉ A

/-- A cycle of odd length. -/
def IsOddCycle (G : SimpleGraph V) {a : V} (c : G.Walk a a) : Prop :=
  c.IsCycle ∧ Odd c.length

/-- `G` has a cycle of length `n`. -/
def HasCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ c.length = n

/--
The circumference of a finite graph: the greatest cycle length, or `0` if
there is no cycle.
-/
noncomputable def circumference (G : SimpleGraph V) [Fintype V] : ℕ :=
  letI := Classical.decPred (fun n => HasCycleLength G n)
  Nat.findGreatest (fun n => HasCycleLength G n) (Fintype.card V)

/-- A chord of a cycle is an edge joining two vertices of the cycle but not lying on it. -/
def IsChordOfCycle (G : SimpleGraph V) {a : V} (c : G.Walk a a) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ e ∉ c.edgeSet ∧ ∃ x ∈ c.support, ∃ y ∈ c.support, e = s(x, y)

/-- An induced cycle is a cycle with no chord in its ambient graph. -/
def IsInducedCycle (G : SimpleGraph V) {a : V} (c : G.Walk a a) : Prop :=
  c.IsCycle ∧ ∀ e : Sym2 V, ¬ IsChordOfCycle G c e

/-- Diestel's Moore-bound expression `n₀(d,g)`. -/
noncomputable def n0 (d : ℝ) (g : ℕ) : ℝ :=
  let r := g / 2
  if Odd g then
    1 + d * ((Finset.range r).sum fun i => (d - 1) ^ i)
  else
    2 * ((Finset.range r).sum fun i => (d - 1) ^ i)

/-- A vertex set `S` separates `A` from `B` if every `A`-`B` path meets `S`. -/
def VertexSetSeparates (G : SimpleGraph V) (S A B : Set V) : Prop :=
  ∀ ⦃a b : V⦄ (p : G.Walk a b), IsABPath G p A B → ∃ x : V, x ∈ p.support ∧ x ∈ S

/-- An edge set `F` separates `A` from `B` if every `A`-`B` path uses an edge of `F`. -/
def EdgeSetSeparates (G : SimpleGraph V) (F : Set (Sym2 V)) (A B : Set V) : Prop :=
  ∀ ⦃a b : V⦄ (p : G.Walk a b), IsABPath G p A B → ∃ e : Sym2 V, e ∈ p.edgeSet ∧ e ∈ F

/-- A vertex set separates two specified vertices, neither of which lies in the separator. -/
def SeparatesVertices (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ VertexSetSeparates G S {a} {b}

/-- A vertex separator: a vertex set separating some two vertices. -/
def IsSeparator (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ a b : V, a ≠ b ∧ SeparatesVertices G S a b

/-- A cutvertex separates two other vertices that were reachable before its deletion. -/
def IsCutvertex (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.Reachable a b ∧ SeparatesVertices G {v} a b

/-- A separation `{A,B}` of `G`: the sides cover all vertices and no edge crosses outside overlap. -/
def IsSeparation (G : SimpleGraph V) (A B : Set V) : Prop :=
  A ∪ B = Set.univ ∧
    ∀ ⦃a b : V⦄, a ∈ A → a ∉ B → b ∈ B → b ∉ A → ¬ G.Adj a b

/-- A proper separation has vertices on both exclusive sides. -/
def IsProperSeparation (G : SimpleGraph V) (A B : Set V) : Prop :=
  IsSeparation G A B ∧ (A \ B).Nonempty ∧ (B \ A).Nonempty

/-- The order of a separation, `|A ∩ B|`. -/
noncomputable def separation_order (A B : Set V) : ℕ :=
  (A ∩ B).ncard

/-- Delete a set of vertices by taking the induced graph on its complement. -/
abbrev delete_vertices (G : SimpleGraph V) (S : Set V) : SimpleGraph (Sᶜ : Set V) :=
  G.induce (Sᶜ : Set V)

/-- Diestel's `k`-connectedness for finite simple graphs. -/
def IsKConnected (G : SimpleGraph V) [Finite V] (k : ℕ) : Prop :=
  k < Nat.card V ∧ ∀ S : Set V, S.ncard < k → (delete_vertices G S).Connected

/-- Diestel's vertex-connectivity `κ(G)`, as the greatest `k` with `G` `k`-connected. -/
noncomputable def vertex_connectivity (G : SimpleGraph V) [Finite V] : ℕ :=
  letI := Classical.decPred (fun k => IsKConnected G k)
  Nat.findGreatest (fun k => IsKConnected G k) (Nat.card V)

/-- Diestel's `ℓ`-edge-connectedness, with the non-trivial order condition made explicit. -/
def IsLEdgeConnected (G : SimpleGraph V) [Finite V] (l : ℕ) : Prop :=
  1 < Nat.card V ∧ G.IsEdgeConnected l

/-- Diestel's edge-connectivity `λ(G)`. -/
noncomputable def edge_connectivity (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℕ :=
  letI := Classical.decPred (fun l => IsLEdgeConnected G l)
  Nat.findGreatest (fun l => IsLEdgeConnected G l) (#G.edgeFinset + 1)

/-- A leaf is a vertex of degree one. -/
def IsLeaf (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (v : V) : Prop :=
  G.degree v = 1

/--
The tree-order associated with a root `r`: `x ≤ y` when `x` lies on a
path from `r` to `y`. This becomes a partial order when the graph is a tree.
-/
def TreeOrder (T : SimpleGraph V) (r x y : V) : Prop :=
  ∃ p : T.Walk r y, p.IsPath ∧ x ∈ p.support

/-- Comparability in the tree-order rooted at `r`. -/
def TreeComparable (T : SimpleGraph V) (r x y : V) : Prop :=
  TreeOrder T r x y ∨ TreeOrder T r y x

/-- Down-closure in the rooted tree-order. -/
def down_closure (T : SimpleGraph V) (r y : V) : Set V :=
  {x | TreeOrder T r x y}

/-- Up-closure in the rooted tree-order. -/
def up_closure (T : SimpleGraph V) (r x : V) : Set V :=
  {y | TreeOrder T r x y}

/--
A normal spanning tree of `G`: a spanning tree `T ≤ G` rooted at `r` such
that adjacent vertices of `G` are comparable in the tree-order of `T`.
-/
def IsNormalSpanningTree (G T : SimpleGraph V) (r : V) : Prop :=
  T ≤ G ∧ T.IsTree ∧ ∀ ⦃x y : V⦄, G.Adj x y → TreeComparable T r x y

/-- A minor model of `X` in `G`, given by connected disjoint branch sets. -/
structure Model (X : SimpleGraph W) (G : SimpleGraph V) where
  branchSet : W → Set V
  nonempty : ∀ x : W, (branchSet x).Nonempty
  pairwise_disjoint : Pairwise fun x y => Disjoint (branchSet x) (branchSet y)
  connected : ∀ x : W, (G.induce (branchSet x)).Connected
  adjacent :
    ∀ ⦃x y : W⦄, X.Adj x y →
      ∃ v ∈ branchSet x, ∃ w ∈ branchSet y, G.Adj v w

/-- The ordinary minor relation, represented by a minor model. -/
def IsMinor (X : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (Model X G)

/--
A topological minor model: vertices of `X` are embedded in `G`, and each
edge of `X` is represented by a path in `G`.

The disjointness condition records Diestel's requirement that edge paths
meet only where forced by common branch vertices.
-/
structure TopologicalModel (X : SimpleGraph W) (G : SimpleGraph V) where
  vertexMap : W ↪ V
  edgePath : ∀ ⦃x y : W⦄, X.Adj x y → G.Walk (vertexMap x) (vertexMap y)
  edgePath_isPath : ∀ ⦃x y : W⦄ (hxy : X.Adj x y), (edgePath hxy).IsPath
  inner_disjoint :
    ∀ ⦃x y z w : W⦄ (hxy : X.Adj x y) (hzw : X.Adj z w),
      s(x, y) ≠ s(z, w) →
        Disjoint (walk_inner_vertices (edgePath hxy)) (walk_inner_vertices (edgePath hzw))
  branch_not_inner :
    ∀ ⦃x y z : W⦄ (hxy : X.Adj x y), vertexMap z ∈ walk_inner_vertices (edgePath hxy) → False

/-- The topological-minor relation, represented by a topological model. -/
def IsTopologicalMinor (X : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (TopologicalModel X G)

/-- A closed walk traversing every edge of `G` exactly once. -/
def IsEulerTour (G : SimpleGraph V) [DecidableEq V] {a : V} (p : G.Walk a a) : Prop :=
  p.IsEulerian

/-- A graph is Eulerian if it has an Euler tour. -/
def IsEulerian (G : SimpleGraph V) [DecidableEq V] : Prop :=
  ∃ a : V, ∃ p : G.Walk a a, IsEulerTour G p

/-- The vertex space over `𝔽₂`. -/
abbrev VertexSpace (V : Type u) :=
  V → ZMod 2

/-- The edge space over `𝔽₂`, indexed by the actual edge set of `G`. -/
abbrev EdgeSpace (G : SimpleGraph V) :=
  G.edgeSet → ZMod 2

/-- The standard dot product on the edge space over `𝔽₂`. -/
noncomputable def edge_inner (G : SimpleGraph V) [Fintype G.edgeSet]
    (F D : EdgeSpace G) : ZMod 2 :=
  ∑ e : G.edgeSet, F e * D e

/-- Orthogonal complement of a subspace of the edge space. -/
noncomputable def edge_orthogonal (G : SimpleGraph V) [Fintype G.edgeSet]
    (S : Submodule (ZMod 2) (EdgeSpace G)) : Set (EdgeSpace G) :=
  {D | ∀ F ∈ S, edge_inner G F D = 0}

/-- The characteristic vector of a set of edges. -/
noncomputable def edge_indicator (G : SimpleGraph V) (F : Set G.edgeSet) : EdgeSpace G :=
  letI := Classical.decPred (fun e : G.edgeSet => e ∈ F)
  fun e => if e ∈ F then 1 else 0

/-- The edge-space vector represented by a cycle. -/
noncomputable def cycle_vector (G : SimpleGraph V) {a : V} (c : G.Walk a a) : EdgeSpace G :=
  letI := Classical.decPred (fun e : G.edgeSet => (e : Sym2 V) ∈ c.edgeSet)
  fun e => if (e : Sym2 V) ∈ c.edgeSet then 1 else 0

/-- The cycle space of `G`, spanned by edge sets of cycles. -/
noncomputable def cycle_space (G : SimpleGraph V) : Submodule (ZMod 2) (EdgeSpace G) :=
  Submodule.span (ZMod 2)
    {F | ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ F = cycle_vector G c}

/-- The cut determined by a bipartition side `A`. -/
def cut_edges (G : SimpleGraph V) (A : Set V) : Set G.edgeSet :=
  {e | ∃ x ∈ A, ∃ y ∈ Aᶜ, (e : Sym2 V) = s(x, y)}

/-- A cut in `G`, represented by the edge set crossing a non-trivial bipartition. -/
def IsCut (G : SimpleGraph V) (F : Set G.edgeSet) : Prop :=
  ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧ F = cut_edges G A

/-- The edge-space vector represented by a cut. -/
noncomputable def cut_vector (G : SimpleGraph V) (A : Set V) : EdgeSpace G :=
  edge_indicator G (cut_edges G A)

/-- The cut space of `G`, generated by all cuts. -/
noncomputable def cut_space (G : SimpleGraph V) : Submodule (ZMod 2) (EdgeSpace G) :=
  Submodule.span (ZMod 2) {F | ∃ A : Set V, F = cut_vector G A}

/-- A bond is a minimal non-empty cut. -/
def IsBond (G : SimpleGraph V) (F : Set G.edgeSet) : Prop :=
  IsCut G F ∧ F.Nonempty ∧
    ∀ ⦃D : Set G.edgeSet⦄, IsCut G D → D.Nonempty → D ⊆ F → F ⊆ D

/-- The atomic cut at a vertex. -/
def atomic_cut (G : SimpleGraph V) (v : V) : Set G.edgeSet :=
  cut_edges G {v}

/-- A spanning tree of `G`, represented as a spanning subgraph on the same vertex type. -/
def IsSpanningTree (G T : SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree

/-- A chord of a spanning tree `T` in `G`. -/
def IsTreeChord (G T : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ e ∉ T.edgeSet

/-- A fundamental cycle of a chord `e` with respect to a spanning tree `T`. -/
def IsFundamentalCycle (G T : SimpleGraph V) (e : Sym2 V) {a : V}
    (c : G.Walk a a) : Prop :=
  IsSpanningTree G T ∧ IsTreeChord G T e ∧ c.IsCycle ∧ e ∈ c.edgeSet ∧
    ∀ f : Sym2 V, f ∈ c.edgeSet → f = e ∨ f ∈ T.edgeSet

end Chapter01
end Diestel
