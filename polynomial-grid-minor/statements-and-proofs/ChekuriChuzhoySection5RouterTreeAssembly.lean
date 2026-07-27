import «statements-and-proofs».ChekuriChuzhoySection5EndpointThinning
import «statements-and-proofs».ChekuriChuzhoySection5Phase1Bundle
import «statements-and-proofs».ChekuriChuzhoySection5TreeAssembly

/-!
# Endpoint-thinned router skeleton on an auxiliary tree

The terminal skeleton produced in Phase 1 is internally disjoint but may
share router endpoints.  This module simultaneously thins all edges of a
degree-three auxiliary tree and promotes the resulting oriented paths to the
fully node-disjoint `ClusterPathSkeleton` consumed by the existing Section 5
tree assembly.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5RouterTreeAssembly

universe u

open ChekuriChuzhoySection5ClusterSkeleton
open ChekuriChuzhoySection5EndpointThinning
open ChekuriChuzhoySection5Phase1Bundle
open ChekuriChuzhoySection5RouterSkeleton
open ChekuriChuzhoySection5TerminalSkeleton

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {m Delta : Nat}
variable {cluster : Fin m → Finset V}

/-- Unoriented edges of the chosen auxiliary tree. -/
abbrev TreeEdgeRequest (T : _root_.SimpleGraph (Fin m)) :=
  {p : Sym2 (Fin m) // p ∈ T.edgeFinset}

noncomputable def requestLeft (T : _root_.SimpleGraph (Fin m))
    (r : TreeEdgeRequest T) : Fin m := r.1.out.1

noncomputable def requestRight (T : _root_.SimpleGraph (Fin m))
    (r : TreeEdgeRequest T) : Fin m := r.1.out.2

theorem request_adj (T : _root_.SimpleGraph (Fin m))
    (r : TreeEdgeRequest T) : T.Adj (requestLeft T r) (requestRight T r) := by
  have hp := r.2
  rw [_root_.SimpleGraph.mem_edgeFinset] at hp
  rw [← r.1.out_eq] at hp
  simpa only [requestLeft, requestRight, _root_.SimpleGraph.mem_edgeSet] using hp

theorem request_left_ne_right (T : _root_.SimpleGraph (Fin m))
    (r : TreeEdgeRequest T) : requestLeft T r ≠ requestRight T r :=
  (request_adj T r).ne

/-- A named selected edge, tagged by its unique auxiliary-tree request. -/
abbrev ExactTreeEdge
    (S : RouterPathSkeleton G cluster) (T : _root_.SimpleGraph (Fin m))
    {width : Nat}
    (candidate : TreeEdgeRequest T → Finset S.graph.Edge)
    (A : RouterExactBundleFamily S Finset.univ (requestLeft T)
      (requestRight T) candidate width) :=
  Σ r : TreeEdgeRequest T, {e : S.graph.Edge // e ∈ A.exact r}

/-- The selected exact bundles as a finite edge-indexed graph.  Every host
path is oriented from the canonical `Sym2.out` left endpoint to its right
endpoint. -/
noncomputable def exactTreeGraph
    (S : RouterPathSkeleton G cluster) (T : _root_.SimpleGraph (Fin m))
    {width : Nat}
    (candidate : TreeEdgeRequest T → Finset S.graph.Edge)
    (A : RouterExactBundleFamily S Finset.univ (requestLeft T)
      (requestRight T) candidate width) :
    FiniteEdgeIndexedGraph (Fin m) where
  Edge := ExactTreeEdge S T candidate A
  left := fun e => requestLeft T e.1
  right := fun e => requestRight T e.1
  end_ne := fun e => request_left_ne_right T e.1

noncomputable def exactTreeHostPath
    (S : RouterPathSkeleton G cluster) (T : _root_.SimpleGraph (Fin m))
    {width : Nat}
    (candidate : TreeEdgeRequest T → Finset S.graph.Edge)
    (A : RouterExactBundleFamily S Finset.univ (requestLeft T)
      (requestRight T) candidate width)
    (e : (exactTreeGraph S T candidate A).Edge) : GraphPath G :=
  orientedHostPathAt S (requestLeft T e.1) e.2.1

/-- Exact bundles on distinct tree edges, and distinct members of one exact
bundle, are node-disjoint after orientation. -/
theorem exactTreeHostPath_nodeDisjoint
    (S : RouterPathSkeleton G cluster) (T : _root_.SimpleGraph (Fin m))
    (global : Finset S.graph.Edge) (htransversal : S.IsGroupTransversal global)
    {width : Nat}
    (candidate : TreeEdgeRequest T → Finset S.graph.Edge)
    (hcandidateGlobal : ∀ r, candidate r ⊆ global)
    (hcandidateJoins : ∀ r, ∀ e ∈ candidate r,
      S.graph.Joins e (requestLeft T r) (requestRight T r))
    (hclusterDisjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (A : RouterExactBundleFamily S Finset.univ (requestLeft T)
      (requestRight T) candidate width)
    {e f : (exactTreeGraph S T candidate A).Edge} (hef : e ≠ f) :
    (exactTreeHostPath S T candidate A e).NodeDisjoint
      (exactTreeHostPath S T candidate A f) := by
  classical
  have horient (a : (exactTreeGraph S T candidate A).Edge) :
      (exactTreeHostPath S T candidate A a).vertexSet =
        (S.hostPath a.2.1).vertexSet := by
    by_cases h : S.graph.left a.2.1 = requestLeft T a.1 <;>
      simp [exactTreeHostPath, orientedHostPathAt, h]
  rw [GraphPath.NodeDisjoint, horient e, horient f]
  by_cases hrequest : e.1 = f.1
  · have hfExact : f.2.1 ∈ A.exact e.1 := by
      simpa [hrequest] using f.2.2
    have hedge : e.2.1 ≠ f.2.1 := by
      intro h
      apply hef
      cases e with
      | mk er ee =>
          cases f with
          | mk fr fe =>
              dsimp at hrequest h ⊢
              subst fr
              have hefe : ee = fe := Subtype.ext h
              subst fe
              rfl
    exact routerHostPath_nodeDisjoint_of_endpoint_injective S
      (request_left_ne_right T e.1)
      (hclusterDisjoint _ _ (request_left_ne_right T e.1)) global
      (A.exact e.1) htransversal
      ((A.exact_subset e.1 (Finset.mem_univ _)).trans
        (hcandidateGlobal e.1))
      (fun a ha => hcandidateJoins e.1 a
        (A.exact_subset e.1 (Finset.mem_univ _) ha))
      (A.left_injective e.1 (Finset.mem_univ _))
      (A.right_injective e.1 (Finset.mem_univ _))
      e.2.2 hfExact hedge
  · exact A.hostPath_nodeDisjoint_of_ne S global htransversal Finset.univ
      (requestLeft T) (requestRight T) candidate
      (fun r _ => hcandidateGlobal r)
      (fun r _ a ha => hcandidateJoins r a ha)
      (Finset.mem_univ _) (Finset.mem_univ _) hrequest e.2.2 f.2.2

/-- Promotion of a globally endpoint-thinned router family to the strong
node-disjoint cluster skeleton API.  Singleton groups make every subsequent
global transversal retain all exact paths. -/
noncomputable def exactTreeClusterPathSkeleton
    (S : RouterPathSkeleton G cluster) (T : _root_.SimpleGraph (Fin m))
    (global : Finset S.graph.Edge) (htransversal : S.IsGroupTransversal global)
    {width : Nat}
    (candidate : TreeEdgeRequest T → Finset S.graph.Edge)
    (hcandidateGlobal : ∀ r, candidate r ⊆ global)
    (hcandidateJoins : ∀ r, ∀ e ∈ candidate r,
      S.graph.Joins e (requestLeft T r) (requestRight T r))
    (hclusterDisjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (A : RouterExactBundleFamily S Finset.univ (requestLeft T)
      (requestRight T) candidate width) :
    ClusterPathSkeleton G cluster where
  graph := exactTreeGraph S T candidate A
  hostPath := exactTreeHostPath S T candidate A
  host_source_mem := by
    intro e
    simpa [exactTreeHostPath] using
      A.left_mem e.1 (Finset.mem_univ _) e.2.1 e.2.2
  host_target_mem := by
    intro e
    change (orientedHostPathAt S (requestLeft T e.1) e.2.1).target ∈
      cluster (requestRight T e.1)
    rw [orientedHostPathAt_target S (request_left_ne_right T e.1) e.2.1
      (hcandidateJoins e.1 e.2.1
        (A.exact_subset e.1 (Finset.mem_univ _) e.2.2))]
    exact A.right_mem e.1 (Finset.mem_univ _) e.2.1 e.2.2
  host_source_interface := by
    intro e
    simpa [exactTreeHostPath] using
      routerEndpointAt_mem_interfaceVertices_of_joins S
        (request_left_ne_right T e.1)
        (hclusterDisjoint _ _ (request_left_ne_right T e.1)) e.2.1
        (hcandidateJoins e.1 e.2.1
          (A.exact_subset e.1 (Finset.mem_univ _) e.2.2))
  host_target_interface := by
    intro e
    change (orientedHostPathAt S (requestLeft T e.1) e.2.1).target ∈
      ChekuriChuzhoySection5Clustering.interfaceVertices G
        (cluster (requestRight T e.1))
    rw [orientedHostPathAt_target S (request_left_ne_right T e.1) e.2.1
      (hcandidateJoins e.1 e.2.1
        (A.exact_subset e.1 (Finset.mem_univ _) e.2.2))]
    exact
      routerEndpointAt_mem_interfaceVertices_of_joins S
        (request_left_ne_right T e.1).symm
        (hclusterDisjoint _ _ (request_left_ne_right T e.1)).symm e.2.1
        ((S.graph.joins_comm e.2.1 _ _).mpr
          (hcandidateJoins e.1 e.2.1
            (A.exact_subset e.1 (Finset.mem_univ _) e.2.2)))
  groups := (⊥ : Finpartition (Finset.univ : Finset
    (exactTreeGraph S T candidate A).Edge))
  internally_disjoint_clusters := by
    intro e r
    by_cases h : S.graph.left e.2.1 = requestLeft T e.1
    · simpa [exactTreeHostPath, orientedHostPathAt, h] using
        S.internally_disjoint_clusters e.2.1 r
    · simpa [exactTreeHostPath, orientedHostPathAt, h] using
        (GraphPath.reverse_internallyDisjointFromSet
          (S.hostPath e.2.1) (cluster r)).2
          (S.internally_disjoint_clusters e.2.1 r)
  one_per_group_node_disjoint := by
    intro _selected _hselected e _he f _hf hef
    exact exactTreeHostPath_nodeDisjoint S T global htransversal candidate
      hcandidateGlobal hcandidateJoins hclusterDisjoint A hef

theorem exactTreeClusterPathSkeleton_groupSizeAtMost_one
    (S : RouterPathSkeleton G cluster) (T : _root_.SimpleGraph (Fin m))
    (global : Finset S.graph.Edge) (htransversal : S.IsGroupTransversal global)
    {width : Nat}
    (candidate : TreeEdgeRequest T → Finset S.graph.Edge)
    (hcandidateGlobal : ∀ r, candidate r ⊆ global)
    (hcandidateJoins : ∀ r, ∀ e ∈ candidate r,
      S.graph.Joins e (requestLeft T r) (requestRight T r))
    (hclusterDisjoint : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (A : RouterExactBundleFamily S Finset.univ (requestLeft T)
      (requestRight T) candidate width) :
    (exactTreeClusterPathSkeleton S T global htransversal candidate
      hcandidateGlobal hcandidateJoins hclusterDisjoint A).GroupSizeAtMost 1 := by
  intro U hU
  dsimp only [exactTreeClusterPathSkeleton] at hU
  rw [Finpartition.parts_bot] at hU
  rcases Finset.mem_map.mp hU with ⟨e, _he, rfl⟩
  exact (Finset.card_singleton e).le

end ChekuriChuzhoySection5RouterTreeAssembly
end SimpleGraph
