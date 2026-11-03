import Yau.Proofs.F05LocalC2Transfer

/-! The local equality used in physical patch gluing also transfers the
literal original operator, including its closed-time derivative. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_local_linearOp_transfer {n : ℕ} {D : Set (Space n)} {T : ℝ}
    {u v : Point n → ℝ} (hu : C2 (cylinder univ 0 T) u)
    (hNear : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 T, u (y,t) = v (y,t))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder D 0 T) :
    linearOp (cylinder univ 0 T) a b u p = linearOp (cylinder D 0 T) a b v p := by
  obtain ⟨hC2,hV,hG,hH,hK⟩ := F05_local_c2_transfer hu hNear
  unfold linearOp
  rw [hG hp,hH hp,hK hp]

end Yau.Proofs.F05Aux
