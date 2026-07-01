import TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.BonnetDepresLower
import TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.Partition

/-!
# Contract for exponential twin-width over treewidth

This file exposes the clean axiom-free contract surface for the
Bonnet--Déprés result.  The lower-bound proof is in
`TwinWidth.Graph.BonnetDepresLower`; this file keeps the public surface to the
final separation theorem.
-/

namespace TwinWidth
namespace SimpleGraph
namespace TwinWidthTreewidthContract

private theorem exists_graph_treewidth_linear_twin_width_exponential_of_twinWidth_lower_bound
    (hBD_twinWidth :
      ∀ k : ℕ, 2 ^ k < twinWidth (bonnetDepresGraph k))
    (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : _root_.SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G := by
  let V : Type := BonnetDepresVertex k
  let G : _root_.SimpleGraph V := bonnetDepresGraph k
  exact ⟨V, inferInstance, inferInstance, G, bonnetDepres_treewidth_le k, hBD_twinWidth k⟩

/-- Equivalent contract surface for the lower-bound proof: it is enough to
show that no contraction sequence of width `2^k` exists for the concrete
Bonnet--Déprés graph. -/
private theorem exists_graph_treewidth_linear_twin_width_exponential_of_no_bounded_sequence
    (hBD_noSequence :
      ∀ k : ℕ, ¬ HasTwinWidthAtMost (bonnetDepresGraph k) (2 ^ k))
    (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : _root_.SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G := by
  exact exists_graph_treewidth_linear_twin_width_exponential_of_twinWidth_lower_bound
    (fun k =>
      _root_.TwinWidth.SimpleGraph.lt_twinWidth_of_not_hasTwinWidthAtMost
        (hBD_noSequence k)) k

/-- Axiom-free final contract: for every exponent `k`, there is a finite simple
graph whose treewidth is at most `2 * k + 4` while twin-width is strictly
greater than `2^k`. -/
theorem exists_graph_treewidth_linear_twin_width_exponential
    (k : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : _root_.SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G :=
  exists_graph_treewidth_linear_twin_width_exponential_of_no_bounded_sequence
    (fun k =>
      _root_.TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_not_hasTwinWidthAtMost_two_pow k) k

end TwinWidthTreewidthContract
end SimpleGraph
end TwinWidth
