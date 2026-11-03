import Yau.Proofs.P04PoleWeightModel
import Yau.Proofs.P04SquaredNormHessian

noncomputable section
open Set
open scoped Topology ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

/-- Epsilon zero is included away from the pole. This is the compact
annulus regularity needed for bounds independent of regularization. -/
theorem regularizedPoleModel_joint_off_center {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (z₀ : ComplexVector n) (c : ℝ)
    (p : ℝ × ComplexVector n) (hp : p.2 ≠ z₀) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ComplexVector n => regularizedPoleModel χ z₀ c q.1 q.2) p := by
  have hq : ContDiffAt ℝ ∞ (fun q : ℝ × ComplexVector n => ‖q.2-z₀‖^2+q.1^2) p :=
    ((contDiffAt_snd.sub contDiffAt_const).norm_sq (𝕜 := ℝ)).add (contDiffAt_fst.pow 2)
  have hpos : 0 < ‖p.2-z₀‖^2+p.1^2 := by
    have H := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
    positivity
  exact (contDiffAt_const.mul (hχ.contDiffAt.comp p contDiffAt_snd)).mul (hq.log hpos.ne')

/-- Freezing epsilon in an actual joint Hessian introduces no second
acceleration term. Both derivative slots remain the original real slots. -/
theorem secondFDeriv_fixed_parameter {F : ℝ × ComplexVector n → ℝ} {ε : ℝ}
    {z : ComplexVector n} (hF : ContDiffAt ℝ 2 F (ε,z)) (v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y => F (ε,y))) z v w =
      fderiv ℝ (fderiv ℝ F) (ε,z) (0,v) (0,w) := by
  have hi : ContDiffAt ℝ 2 (fun y : ComplexVector n => (ε,y)) z :=
    contDiffAt_const.prodMk contDiffAt_id
  have hD (y : ComplexVector n) : fderiv ℝ (fun y : ComplexVector n => (ε,y)) y =
      ContinuousLinearMap.inr ℝ ℝ (ComplexVector n) := by
    exact ((hasFDerivAt_const ε y).prodMk (hasFDerivAt_id y)).fderiv
  have hDD : fderiv ℝ (fderiv ℝ (fun y : ComplexVector n => (ε,y))) z=0 := by
    rw [show fderiv ℝ (fun y : ComplexVector n => (ε,y)) =
      fun _ => ContinuousLinearMap.inr ℝ ℝ (ComplexVector n) from funext hD]
    exact (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ (ComplexVector n)) z).fderiv
  have HH := L18Aux.secondFDeriv_comp hi hF v w
  rw [hD,hDD] at HH
  simpa only [Function.comp_def,ContinuousLinearMap.inr_apply,ContinuousLinearMap.zero_apply,
    map_zero,add_zero] using HH

end Yau.Proofs.P04Aux
