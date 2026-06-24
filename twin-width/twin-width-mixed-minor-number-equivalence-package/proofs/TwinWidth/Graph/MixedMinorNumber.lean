import TwinWidth.Matrix.OrderedAdjacency








namespace TwinWidth
namespace SimpleGraph


theorem exists_vertexOrder_card (V : Type*) [Fintype V] :
    Nonempty (VertexOrder V (Fintype.card V)) := by
  classical
  exact ⟨⟨(Fintype.equivFin V).symm⟩⟩


theorem exists_orderedAdjacencyMixedNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ k, ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ = k := by
  classical
  let σ : VertexOrder V (Fintype.card V) := ⟨(Fintype.equivFin V).symm⟩
  exact ⟨Matrix.orderedAdjacencyMixedNumber G σ, σ, rfl⟩



noncomputable def mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℕ :=
  by
    classical
    exact Nat.find (exists_orderedAdjacencyMixedNumber G)


theorem exists_order_mixedNumber_eq_mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ = mixedMinorNumber G := by
  classical
  simpa [mixedMinorNumber] using Nat.find_spec (exists_orderedAdjacencyMixedNumber G)



theorem mixedMinorNumber_le_orderedAdjacencyMixedNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (σ : VertexOrder V (Fintype.card V)) :
    mixedMinorNumber G ≤ Matrix.orderedAdjacencyMixedNumber G σ := by
  classical
  exact Nat.find_min' (exists_orderedAdjacencyMixedNumber G)
    ⟨σ, rfl⟩

theorem mixedMinorNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    mixedMinorNumber G ≤ Fintype.card V := by
  classical
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  rw [← hσ]
  simpa [Matrix.orderedAdjacencyMixedNumber] using
    (Matrix.matrixMixedNumber_le_min_card (Matrix.orderedAdjacency G σ))

end SimpleGraph
end TwinWidth
