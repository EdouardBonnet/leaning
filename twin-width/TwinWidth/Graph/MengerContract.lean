import TwinWidth.Graph.MengerDefs

/-!
# Contract for Finite Vertex-Menger

This contract exposes one statement: the finite vertex-Menger alternative for
ordinary `(S,T)`-separators.  The full proof belongs in
`TwinWidth.Graph.Menger`; downstream modules should import that full file once
the theorem is available there.
-/

namespace TwinWidth
namespace SimpleGraph
namespace MengerContract

universe u

/-- Finite vertex-Menger, in its natural path/separator alternative form:
for every `k`, either there are `k` pairwise vertex-disjoint paths from `S` to
`T`, or some `(S,T)`-separator has fewer than `k` vertices. -/
axiom finite_vertex_menger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) (k : ℕ),
      HasDisjointSTPaths G S T k ∨
        ∃ X : Finset V, X.card < k ∧ STSeparator G S T X

end MengerContract
end SimpleGraph
end TwinWidth
