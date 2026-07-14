import Mathlib.Data.Fintype.Basic

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace VertexOrder

universe u

/-- A vertex order of length n is an equivalence between positions Fin n
and the vertex type. -/
def Order (V : Type u) (n : ℕ) : Type u :=
  Fin n ≃ V

end VertexOrder
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
