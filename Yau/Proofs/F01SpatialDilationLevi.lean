import Yau.Proofs.F01LeviChartNaturality

/-! The Ricci term of the actually dilated background is multiplied by
the square of the spatial scale. The time rescaling can therefore use the
original initial-surface equation without inserting a different background. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem linearMatrix_real_smul_id (ρ : ℝ) :
    linearMatrix ((ρ : ℂ) • ContinuousLinearMap.id ℂ (Space n)) =
      (ρ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  simp [linearMatrix, stdVec, EuclideanSpace.single, Matrix.one_apply]

theorem leviC_spatial_dilation {q : Space n → ℝ} {ρ : ℝ} {z : Space n}
    (hq : ContDiffAt ℝ 2 q (ρ • z)) :
    leviC (fun w => q (ρ • w)) z = ((ρ ^ 2 : ℝ) : ℂ) • leviC q (ρ • z) := by
  let T : Space n → Space n := fun w => (ρ : ℂ) • w
  have hT : ContDiffAt ℂ 2 T z := by dsimp only [T]; fun_prop
  have heq (w : Space n) : T w = ρ • w := by
    dsimp only [T]
    exact Complex.coe_smul ρ w
  have hd : fderiv ℂ T z = (ρ : ℂ) • ContinuousLinearMap.id ℂ (Space n) :=
    ((hasFDerivAt_id z).const_smul (ρ : ℂ)).fderiv
  have h := leviC_comp hT (by simpa only [heq] using hq)
  rw [hd, linearMatrix_real_smul_id] at h
  have hstar : star (ρ : ℂ) = (ρ : ℂ) := Complex.conj_ofReal ρ
  simpa only [Function.comp_def, heq, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, starRingEnd_apply, hstar,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, Complex.ofReal_pow, pow_two, Complex.ofReal_mul] using h

theorem backgroundRicci_spatial_dilation
    (A : Space n → Matrix (Fin n) (Fin n) ℂ) {ρ : ℝ} {z : Space n}
    (hA : ContDiffAt ℝ 2 (fun w => Real.log (A w).det.re) (ρ • z)) :
    backgroundRicci (fun w => A (ρ • w)) z =
      ((ρ ^ 2 : ℝ) : ℂ) • backgroundRicci A (ρ • z) := by
  unfold backgroundRicci
  rw [leviC_spatial_dilation hA, smul_neg]

end Yau.NodeProofs.F01Aux
