import Yau.Proofs.C02GraphCoordinateIntertwining
import Yau.LeafProofs.L21OperatorRows

/-! Translation and scalar dilation preserve the actual column equation
after the correction is divided by the same real dilation. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rescaledCorrection (s : ℝ) (a : E) (w : E → F) (z : E) : F :=
  s⁻¹ • (w (a + s • z) - w a)

theorem rescaledCorrection_zero (s : ℝ) (a : E) (w : E → F) :
    rescaledCorrection s a w 0 = 0 := by simp [rescaledCorrection]

theorem rescaledCorrection_contDiff (s : ℝ) (a : E) (w : E → F)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (rescaledCorrection s a w) :=
  ((hw.comp (contDiff_const.add (contDiff_id.const_smul s))).sub contDiff_const).const_smul s⁻¹

theorem rescaledCorrection_hasFDerivAt (s : ℝ) (hs : s ≠ 0) (a : E) (w : E → F) (x : E)
    (hw : DifferentiableAt ℝ w (a + s • x)) :
    HasFDerivAt (rescaledCorrection s a w) (fderiv ℝ w (a + s • x)) x := by
  have hT : HasFDerivAt (fun z : E => a + s • z) (s • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).const_smul s).const_add a
  have h := ((hw.hasFDerivAt.comp x hT).sub_const (w a)).const_smul s⁻¹
  have hD : s⁻¹ • (fderiv ℝ w (a + s • x)).comp (s • ContinuousLinearMap.id ℝ E) =
      fderiv ℝ w (a + s • x) := by
    ext v
    change s⁻¹ • (fderiv ℝ w (a + s • x)) (s • v) = _
    rw [map_smul, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [hD] at h
  exact h

theorem rescaledCorrection_dbarA {n : ℕ}
    (A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (s : ℝ) (hs : s ≠ 0) (a : ComplexVector n) (w : ComplexVector n → ℂ)
    (x : ComplexVector n) (hw : DifferentiableAt ℝ w (a + s • x)) (i : Fin n) :
    Yau.LeafProofs.L21Aux.dbarA (fun z => A (a + s • z)) i (rescaledCorrection s a w) x =
      Yau.LeafProofs.L21Aux.dbarA A i w (a + s • x) := by
  rw [Yau.LeafProofs.L21Aux.dbarA_eq_real_rows, Yau.LeafProofs.L21Aux.dbarA_eq_real_rows,
    (rescaledCorrection_hasFDerivAt s hs a w x hw).fderiv]
  rfl

end Yau.Blueprint.C02Proof
