import TwinWidth.Matrix.MixedNumber
import Mathlib.Combinatorics.SimpleGraph.Basic








namespace TwinWidth


structure VertexOrder (V : Type*) (n : ℕ) where
  
  equiv : Fin n ≃ V

namespace Matrix


noncomputable def orderedAdjacency {V : Type*} {n : ℕ} (G : SimpleGraph V) (σ : VertexOrder V n) :
    _root_.Matrix (Fin n) (Fin n) Bool :=
  by
    classical
    exact fun i j => decide (G.Adj (σ.equiv i) (σ.equiv j))


noncomputable def orderedAdjacencyMixedNumber {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (σ : VertexOrder V n) : ℕ :=
  matrixMixedNumber (orderedAdjacency G σ)

end Matrix
end TwinWidth
