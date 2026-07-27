import «statements-and-proofs».ChekuriChuzhoySection5MinimalHost
import «statements-and-proofs».ChekuriChuzhoySection5Routers

/-!
# The CNS13 failed-router deletion dependency

The nonalgorithmic proof preceding Chekuri--Chuzhoy Section 5.2 cites the
appendix of [CNS13] for one external fact: in an edge-minimal host preserving
the terminal well-linkedness, a large well-linked router cannot fail to send
half its boundary threshold to the terminals.  The cited argument first
produces a deletable host edge from the failed routing cut.

Only that semantic specialization is recorded here.  The paper dependency is
isolated as the proposition `FailedRouterDeletionStatement`; the axiom below
only inhabits that proposition.  No router family, terminal skeleton, tree,
or tree-of-sets output is hidden in the paper dependency.

Replacing `failedRouterDeletion` by a Lean proof of
`FailedRouterDeletionStatement` therefore removes the CNS13 dependency from
the complete downstream closure without changing any Section 5 interface.
-/

namespace SimpleGraph
namespace CNS13

universe u

open ChekuriChuzhoySection5Clustering
open ChekuriChuzhoySection5Routers

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- The fields of a good router that are known before checking its routing to
the terminal set. -/
structure RouterCandidate
    (G : _root_.SimpleGraph V) (terminals router : Finset V)
    (w0 bandwidthCap alphaNum alphaDen : Nat) : Prop where
  terminal_disjoint : Disjoint router terminals
  connected : IsCluster G router
  large : IsLargeCluster G w0 router
  bandwidth :
    TruncatedScaledBandwidth G router bandwidthCap alphaNum alphaDen

/-- The complete CNS13 paper obligation used by WP1C.

This proposition deliberately quantifies over the graph and all source
parameters.  Its conclusion is only the deletable-edge certificate consumed
by edge-minimality; it contains no downstream router-family or tree output. -/
def FailedRouterDeletionStatement : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {terminals router : Finset V}
    {w0 bandwidthCap alphaNum alphaDen : Nat},
      2 ≤ terminals.card →
        (∀ t ∈ terminals, DegreeEquals G t 1) →
          NodeWellLinkedIn G Finset.univ terminals →
            RouterCandidate G terminals router
              w0 bandwidthCap alphaNum alphaDen →
                ¬ RoutesToTerminals G router terminals (w0 / 2) →
                  ∃ a b : V, G.Adj a b ∧
                    NodeWellLinkedIn
                      (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
                      Finset.univ terminals

/-- The single CNS13 paper dependency in the WP1C closure. -/
axiom failedRouterDeletion : FailedRouterDeletionStatement.{u}

/-- The theorem-shaped wrapper used by Section 5.  Its only project axiom is
`failedRouterDeletion`, whose proposition is displayed in full above. -/
theorem exists_deletableEdge_of_failed_router
    {terminals router : Finset V}
    {w0 bandwidthCap alphaNum alphaDen : Nat}
    (hterminalCard : 2 ≤ terminals.card)
    (hterminalDegree : ∀ t ∈ terminals, DegreeEquals G t 1)
    (hterminals : NodeWellLinkedIn G Finset.univ terminals)
    (candidate : RouterCandidate G terminals router
      w0 bandwidthCap alphaNum alphaDen)
    (hfailed :
      ¬ RoutesToTerminals G router terminals (w0 / 2)) :
    ∃ a b : V, G.Adj a b ∧
      NodeWellLinkedIn
        (G.deleteEdges ({s(a, b)} : Set (Sym2 V)))
        Finset.univ terminals :=
  failedRouterDeletion hterminalCard hterminalDegree hterminals candidate hfailed

/-- Edge-minimality converts the external deletion theorem into the routing
field required by `GoodRouter`. -/
theorem RouterCandidate.routes_of_edgeMinimal
    {G0 : _root_.SimpleGraph V}
    {terminals router : Finset V}
    {w0 bandwidthCap alphaNum alphaDen : Nat}
    (M :
      ChekuriChuzhoySection5MinimalHost.EdgeMinimalNodeWellLinkedHost
        G0 terminals)
    (hterminalCard : 2 ≤ terminals.card)
    (hterminalDegree : ∀ t ∈ terminals, DegreeEquals M.H t 1)
    (candidate : RouterCandidate M.H terminals router
      w0 bandwidthCap alphaNum alphaDen) :
    RoutesToTerminals M.H router terminals (w0 / 2) := by
  by_contra hfailed
  rcases exists_deletableEdge_of_failed_router
      hterminalCard hterminalDegree M.nodeWellLinked candidate hfailed with
    ⟨a, b, hab, hdelete⟩
  exact M.deleteEdge_not_nodeWellLinked hab hdelete

/-- Package a candidate in an edge-minimal host as a good router. -/
def RouterCandidate.toGoodRouter_of_edgeMinimal
    {G0 : _root_.SimpleGraph V}
    {terminals router : Finset V}
    {w0 bandwidthCap alphaNum alphaDen : Nat}
    (M :
      ChekuriChuzhoySection5MinimalHost.EdgeMinimalNodeWellLinkedHost
        G0 terminals)
    (hterminalCard : 2 ≤ terminals.card)
    (hterminalDegree : ∀ t ∈ terminals, DegreeEquals M.H t 1)
    (candidate : RouterCandidate M.H terminals router
      w0 bandwidthCap alphaNum alphaDen) :
    GoodRouter M.H terminals router
      w0 bandwidthCap alphaNum alphaDen (w0 / 2) where
  terminal_disjoint := candidate.terminal_disjoint
  connected := candidate.connected
  large := candidate.large
  bandwidth := candidate.bandwidth
  routes := candidate.routes_of_edgeMinimal M hterminalCard hterminalDegree

/-- Simultaneously promote a pairwise-disjoint family of router candidates in
an edge-minimal host.  The only non-structural ingredient is the failed-router
deletion axiom above; no routing or tree-of-sets output is assumed. -/
def goodRouterFamily_of_candidates_edgeMinimal
    {G0 : _root_.SimpleGraph V}
    {terminals : Finset V}
    {count w0 bandwidthCap alphaNum alphaDen : Nat}
    (M :
      ChekuriChuzhoySection5MinimalHost.EdgeMinimalNodeWellLinkedHost
        G0 terminals)
    (hterminalCard : 2 ≤ terminals.card)
    (hterminalDegree : ∀ t ∈ terminals, DegreeEquals M.H t 1)
    (router : Fin count → Finset V)
    (candidate : ∀ i, RouterCandidate M.H terminals (router i)
      w0 bandwidthCap alphaNum alphaDen)
    (hdisjoint : Pairwise fun i j => Disjoint (router i) (router j)) :
    GoodRouterFamily M.H terminals count
      w0 bandwidthCap alphaNum alphaDen (w0 / 2) where
  router := router
  good := fun i =>
    (candidate i).toGoodRouter_of_edgeMinimal
      M hterminalCard hterminalDegree
  pairwise_disjoint := hdisjoint

end CNS13
end SimpleGraph
