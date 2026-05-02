import TwinWidth.Matrix.MarcusTardos

/-!
# Contract statements for Marcus--Tardos

This contract file states only the final finite matrix claim supplied by
`MarcusTardos.lean`.  The full proof file proves this statement without
importing this contract module.
-/

namespace TwinWidth
namespace Matrix
namespace MarcusTardosContract

/-- Marcus--Tardos theorem in the grid-minor form used downstream: for every
grid order `t`, some constant `c` makes density `c * max n m` force a
`t`-grid minor. -/
axiom marcus_tardos_grid_minor_density :
    ∀ t : ℕ, ∃ c : ℕ,
      ∀ {n m : ℕ} (M : _root_.Matrix (Fin n) (Fin m) Bool),
        0 < max n m →
          c * max n m ≤ (oneEntries M).card →
            HasGridMinor M t

end MarcusTardosContract
end Matrix
end TwinWidth
