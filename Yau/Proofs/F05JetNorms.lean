import Yau.Proofs.F05JetComponents
import Yau.Proofs.F05BCFExtension

/-! The inherited product norm controls the literal physical jet budgets.
No unchecked supremum is used to assign the function-space norm. -/

open Set
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05JetComponent_value_bound {α : ℝ} {Q : Set (Point n)}
    (u : F05JetComponent α Q) (p : Point n) : ‖F05BCFFun u.1 p‖ ≤ ‖u‖ :=
  (F05BCFFun_norm_le u.1 p).trans (le_max_left _ _)

theorem F05JetComponent_gradient_bound {α : ℝ} {Q : Set (Point n)}
    (u : F05JetComponent α Q) (p : Point n) : ‖F05BCFFun u.2.1 p‖ ≤ ‖u‖ :=
  (F05BCFFun_norm_le u.2.1 p).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem F05JetComponent_hessian_holderBound {α : ℝ} {Q : Set (Point n)}
    (u : F05JetComponent α Q) : HolderBound α Q (F05BCFFun u.2.2.1.val.1) ‖u‖ := by
  have hNorm : ‖u.2.2.1‖ ≤ ‖u‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have heq : F05BCFFun u.2.2.1.val.1 = vectorHolderFun u.2.2.1 := rfl
  rw [heq]
  exact holderBound_mono_const (vectorHolderFun_holderBound u.2.2.1) hNorm

theorem F05JetComponent_time_holderBound {α : ℝ} {Q : Set (Point n)}
    (u : F05JetComponent α Q) : HolderBound α Q (F05BCFFun u.2.2.2.val.1) ‖u‖ := by
  have hNorm : ‖u.2.2.2‖ ≤ ‖u‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have heq : F05BCFFun u.2.2.2.val.1 = holderGraphFun u.2.2.2 := rfl
  rw [heq]
  exact holderBound_mono_const (holderGraphFun_holderBound u.2.2.2) hNorm

end Yau.Proofs.F05Aux
