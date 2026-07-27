import «statements-and-proofs».EdgeMenger

/-!
# Contract for finite edge-Menger

This contract exposes the exact edge-Menger cut form needed in
Chuzhoy--Tan Section 4.4.  It forwards to the self-contained proof in
`«statements-and-proofs».EdgeMenger`.
-/

namespace SimpleGraph
namespace EdgeMenger

universe u

/-- Finite edge-Menger, cut form.  If there are fewer than `k` edge-disjoint
`A`--`B` paths contained in `C`, then `C` has an `A`--`B` cut of size `< k`. -/
theorem edge_menger_cut_contract : EdgeMengerCutStatement.{u} :=
  edge_menger_cut

end EdgeMenger
end SimpleGraph
