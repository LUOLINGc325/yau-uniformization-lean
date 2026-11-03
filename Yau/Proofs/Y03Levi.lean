import Yau.Proofs.Y03Wirtinger

/-! The exact contract Levi operator in terms of the real second differential. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_wirtBar_apply {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (v h : V) :
    fderiv ℝ (fun w => wirtBar f w v) z h =
      (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) z h v +
        Complex.I * fderiv ℝ (fderiv ℝ f) z h (Complex.I • v)) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv : DifferentiableAt ℝ (fun w => fderiv ℝ f w v) z :=
    hdf.clm_apply (differentiableAt_const v)
  have hIv : DifferentiableAt ℝ (fun w => fderiv ℝ f w (Complex.I • v)) z :=
    hdf.clm_apply (differentiableAt_const (Complex.I • v))
  unfold wirtBar
  rw [fderiv_const_mul (a := fun w => fderiv ℝ f w v + Complex.I * fderiv ℝ f w (Complex.I • v))
      (hv.add (hIv.const_mul Complex.I)) (1 / 2 : ℂ),
    fderiv_fun_add hv (hIv.const_mul Complex.I), fderiv_const_mul hIv,
    fderiv_clm_apply hdf (differentiableAt_const v),
    fderiv_clm_apply hdf (differentiableAt_const (Complex.I • v))]
  simp
  ring

theorem levi_direction_eq_hessian {f : V → ℂ} {z : V}
    (hf : ContDiffAt ℝ 2 f z) (v : V) :
    wirt (fun w => wirtBar f w v) z v =
      (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ f) z v v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v)) := by
  unfold wirt
  rw [fderiv_wirtBar_apply hf, fderiv_wirtBar_apply hf]
  have hsym := (hf.isSymmSndFDerivAt (by norm_num)).eq v (Complex.I • v)
  rw [hsym]
  ring_nf
  simp
  ring

theorem wirtBar_contDiffAt {f : V → ℂ} {z : V}
    (hf : ContDiffAt ℝ 2 f z) (v : V) : ContDiffAt ℝ 1 (fun w => wirtBar f w v) z := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) z := hf.fderiv_right (by norm_num)
  have hv : ContDiffAt ℝ 1 (fun w => fderiv ℝ f w v) z := hdf.clm_apply contDiffAt_const
  have hIv : ContDiffAt ℝ 1 (fun w => fderiv ℝ f w (Complex.I • v)) z :=
    hdf.clm_apply contDiffAt_const
  unfold wirtBar
  exact contDiffAt_const.mul (hv.add (contDiffAt_const.mul hIv))

end Yau.Blueprint.Alignment.Y03Proof
