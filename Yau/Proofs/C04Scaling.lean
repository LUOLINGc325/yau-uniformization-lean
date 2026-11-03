import Yau.Blueprint.Nodes
import Yau.Proofs.F02Elementary

/-! Scaling identities for the actual rescaled fields in RicciWindows. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder MatrixOrder
open Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) (z : ComplexVector n) :
    hMat (scaleField c hc k) x z = (c : ℂ) • hMat k x z := rfl

theorem gMat_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) : gMat (scaleField c hc k) x = (c : ℂ) • gMat k x := rfl

theorem leviC_congr_nhds {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hfg : f =ᶠ[𝓝 z] g) : leviC f z = leviC g z := by
  have hF : (fun y => (f y : ℂ)) =ᶠ[𝓝 z] (fun y => (g y : ℂ)) :=
    hfg.fun_comp Complex.ofReal
  have hdF := hF.fderiv (𝕜 := ℝ)
  ext i j
  have hbar : (fun y => wirtBar (fun x => (f x : ℂ)) y (stdVec i)) =ᶠ[𝓝 z]
      (fun y => wirtBar (fun x => (g x : ℂ)) y (stdVec i)) := by
    filter_upwards [hdF] with y hy
    simp only [wirtBar, hy]
  simp only [leviC, leviMatrix, wirt, hbar.fderiv_eq]

theorem leviC_add_const (f : ComplexVector n → ℝ) (c : ℝ) (z : ComplexVector n) :
    leviC (fun w => f w + c) z = leviC f z := by
  ext i j
  simp only [leviC, leviMatrix, Complex.ofReal_add, wirtBar, fderiv_add_const]

theorem logDet_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    logDet (scaleField c hc k) x z = logDet k x z + n * Real.log c := by
  have hd := LeafProofs.L18Aux.hMat_det_re_pos k x hz
  rw [logDet, hMat_scaleField, Matrix.det_smul]
  simp only [Fintype.card_fin, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Real.log_mul (pow_ne_zero _ hc.ne') hd.ne', Real.log_pow]
  simp only [logDet]
  ring

/-- Constant rescaling preserves the actual coordinate Ricci tensor. -/
theorem ricci_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) : ricci (scaleField c hc k) x = ricci k x := by
  have heq : logDet (scaleField c hc k) x =ᶠ[𝓝 (chartPt x x)]
      fun z => logDet k x z + n * Real.log c := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x)] with z hz
    exact logDet_scaleField c hc k x hz
  rw [ricci, leviC_congr_nhds heq, leviC_add_const]
  rfl

theorem inverse_real_smul (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) : ((c : ℂ) • H)⁻¹ = (c⁻¹ : ℂ) • H⁻¹ := by
  apply Matrix.inv_eq_left_inv
  have hu : IsUnit H.det := hH.isUnit.map Matrix.detMonoidHom
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.ofReal_inv, mul_inv_cancel₀ hcC, one_smul]
  exact Matrix.nonsing_inv_mul _ hu

/-- Scalar curvature scales by the reciprocal of the same positive multiplier. -/
theorem scalar_scaleField (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) : scalarCurvature (scaleField c hc k) x = c⁻¹ * scalarCurvature k x := by
  have hg : (gMat k x).PosDef :=
    LeafProofs.L18Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  rw [scalarCurvature, gMat_scaleField, ricci_scaleField, traceWith,
    inverse_real_smul c hc _ hg]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, scalarCurvature, traceWith]

theorem scalar_normalized (k : HermitianField M) (o : M.Carrier)
    (hR : 0 < scalarCurvature k o) :
    scalarCurvature (scaleField (scalarCurvature k o) hR k) o = 1 := by
  rw [scalar_scaleField, inv_mul_cancel₀ hR.ne']

end Yau.Proofs.C04Aux
