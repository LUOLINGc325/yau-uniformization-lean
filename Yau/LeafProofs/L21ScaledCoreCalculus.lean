import Yau.LeafProofs.L21UnscaledCoercivity
import Yau.LeafProofs.L21ScaledComplex
import Yau.LeafProofs.L21WeightedEnergyBounds

/-! The exact rho-scaled compact complex, with its literal curl correction
and a dimension-dependent bound for D rho. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

theorem contDiff_complex_rho : ContDiff ℝ ∞ (fun x : X n => (rho x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp contDiff_rho

def testRhoMul (hO : IsOpen O) (u : CompactTest O) : CompactTest O :=
  multiplyLocalTest hO contDiff_complex_rho.contDiffOn u

theorem testRhoMul_apply (hO : IsOpen O) (u : CompactTest O) (x : X n) :
    testRhoMul hO u x = (rho x : ℂ) * u x := rfl

theorem testRhoInverse_testRhoMul (u : CompactTest (Metric.ball (0 : X n) 1)) :
    testRhoInverse (testRhoMul Metric.isOpen_ball u) = u := by
  apply compactTest_ext_on
  intro x hx
  rw [testRhoInverse_apply, testRhoMul_apply]
  have hr : (rho x : ℂ) ≠ 0 := by exact_mod_cast (rho_pos hx).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul]

def testScaledS (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) (v : Fin n → CompactTest O) (i j : Fin n) : CompactTest O :=
  testRhoMul hO (testD hO hA i (v j) - testD hO hA j (v i)) -
    multiplyLocalTest hO (contDiffOn_dbarA hO hA i contDiff_complex_rho.contDiffOn) (v j) +
    multiplyLocalTest hO (contDiffOn_dbarA hO hA j contDiff_complex_rho.contDiffOn) (v i)

theorem testScaledS_apply (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) (v : Fin n → CompactTest O) (i j : Fin n) (x : X n) :
    testScaledS hO hA v i j x = degenerateS A (fun y k => v k y) x i j := rfl

def testRhoWedge (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) (v : Fin n → CompactTest O) (i j : Fin n) : CompactTest O :=
  multiplyLocalTest hO (contDiffOn_dbarA hO hA i contDiff_complex_rho.contDiffOn) (v j) -
    multiplyLocalTest hO (contDiffOn_dbarA hO hA j contDiff_complex_rho.contDiffOn) (v i)

theorem test_scaled_curl_identity (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) (v : Fin n → CompactTest O) (i j : Fin n) :
    testD hO hA i (testRhoMul hO (v j)) - testD hO hA j (testRhoMul hO (v i)) =
      testScaledS hO hA v i j +
        multiplyLocalTest hO (a := fun _ => (2 : ℂ)) contDiffOn_const (testRhoWedge hO hA v i j) := by
  apply compactTest_ext_on
  intro x hx
  change dbarA A i (fun y => (rho y : ℂ) * v j y) x -
      dbarA A j (fun y => (rho y : ℂ) * v i y) x =
    (rho x : ℂ) * (dbarA A i (v j) x - dbarA A j (v i) x) -
      dbarA A i (fun y => (rho y : ℂ)) x * v j x +
      dbarA A j (fun y => (rho y : ℂ)) x * v i x +
      2 * (dbarA A i (fun y => (rho y : ℂ)) x * v j x -
        dbarA A j (fun y => (rho y : ℂ)) x * v i x)
  rw [dbarA_mul A i (contDiff_complex_rho.differentiable (by simp) x)
      ((v j).property.1.differentiable (by simp) x),
    dbarA_mul A j (contDiff_complex_rho.differentiable (by simp) x)
      ((v i).property.1.differentiable (by simp) x)]
  ring

theorem dbarA_rho_norm_le (A : X n → Matrix (Fin n) (Fin n) ℂ) {x : X n}
    (hx : x ∈ Metric.ball (0 : X n) 1) (hA : ∀ i j, ‖A x i j‖ ≤ 1) (i : Fin n) :
    ‖dbarA A i (fun y => (rho y : ℂ)) x‖ ≤ 8 * (n : ℝ) := by
  have hD : ‖fderiv ℝ (fun y : X n => (rho y : ℂ)) x‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    rw [fderiv_ofReal_apply (contDiff_rho.differentiable (by simp) x), Complex.norm_real]
    exact ((fderiv ℝ (rho : X n → ℝ) x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_rho_le_two hx) (norm_nonneg _))
  have hh := mixedFrame_rowApply_norm (dbarRealCoefficient A i) (fun y => (rho y : ℂ)) x
    (mixedFrame_row_norm hA i)
  change ‖∑ a : Yau.RIdx n, dbarRealCoefficient A i a x *
    fderiv ℝ (fun y : X n => (rho y : ℂ)) x (Yau.realVec a)‖ ≤ _ at hh
  rw [← dbarA_eq_real_rows] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hD (by positivity)).trans_eq (by ring))

end Yau.LeafProofs.L21Aux
