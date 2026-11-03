import Yau.Proofs.F03WeightGradientFactors

/-! Genuine gradient and Levi estimates for f/u², with a positive decay parameter. -/
noncomputable section
open scoped ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalizedCorrection (u f : M.Carrier → ℝ) (x : M.Carrier) : ℝ := f x*(u x)^(-2:ℤ)

theorem normalizedCorrection_smooth (u f : M.Carrier → ℝ) (hu : SmoothFn u)
    (hu0 : ∀ x,0 < u x) (hf : SmoothFn f) : SmoothFn (normalizedCorrection u f) :=
  fun a => (hf a).mul (smoothFn_inverseSquare_of_pos u hu hu0 a)

theorem normalizedCorrection_gradient_bound (g : HermitianField M)
    (u f : M.Carrier → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) (hf : SmoothFn f)
    (x : M.Carrier) {B v : ℝ} (hB : 0 < B) (hv : 0 < v)
    (hU : Real.sqrt (gradNormSq g u x) ≤ B) (hSize : |f x| ≤ B*(u x)^2/v)
    (hGrad : Real.sqrt (gradNormSq g f x) ≤ B*u x/v) :
    Real.sqrt (gradNormSq g (normalizedCorrection u f) x) ≤ (B+2*B^2)/(u x*v) := by
  have hx0 : 0 < u x := hu0 x
  have hInvValue : (u x)^(-2:ℤ)=1/(u x)^2 := by
    have hh : (u x)^(-2:ℤ)=((u x)^2)⁻¹ := zpow_negSucc (u x) 1
    simpa only [one_div] using hh
  have hInvAbs : |(u x)^(-2:ℤ)|=1/(u x)^2 := by
    rw [hInvValue,abs_of_pos (div_pos zero_lt_one (sq_pos_of_pos (hu0 x)))]
  have hTriangle := sqrt_gradNormSq_mul_le g hf (smoothFn_inverseSquare_of_pos u hu hu0) x
  rw [sqrt_gradNormSq_inverseSquare g u hu hu0 x,hInvAbs] at hTriangle
  apply hTriangle.trans
  calc
    _ ≤ (B*(u x)^2/v)*((2/(u x)^3)*B)+(1/(u x)^2)*(B*u x/v) := by
      gcongr <;> positivity
    _ = _ := by field_simp <;> ring

theorem normalizedCorrection_levi_lower_bound (g : HermitianField M)
    (u f : M.Carrier → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) (hf : SmoothFn f)
    (x : M.Carrier) (D : Herm n) {B v : ℝ} (hB : 0 < B) (hv : 0 < v)
    (hU : Real.sqrt (gradNormSq g u x) ≤ B)
    (hULevi : HermAbsLE (levi u x) (gMat g x) (B/u x))
    (hSize : |f x| ≤ B*(u x)^2/v) (hGrad : Real.sqrt (gradNormSq g f x) ≤ B*u x/v)
    (hFLevi : HermLE (D-Complex.ofReal (B/v) • gMat g x) (levi f x)) :
    HermLE (Complex.ofReal (1/(u x)^2) •
      (D-Complex.ofReal ((B+6*B^2+6*B^3)/v) • gMat g x))
      (levi (normalizedCorrection u f) x) := by
  have hG : (gMat g x).PosSemidef := (hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hInvSmooth := smoothFn_inverseSquare_of_pos u hu hu0
  have hx0 : 0 < u x := hu0 x
  have hInvValue : (u x)^(-2:ℤ)=1/(u x)^2 := by
    have hh : (u x)^(-2:ℤ)=((u x)^2)⁻¹ := zpow_negSucc (u x) 1
    simpa only [one_div] using hh
  have hInvGrad : Real.sqrt (gradNormSq g (fun y => (u y)^(-2:ℤ)) x) ≤ 2*B/(u x)^3 := by
    rw [sqrt_gradNormSq_inverseSquare g u hu hu0 x]
    convert mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 2/(u x)^3) using 1 <;> ring
  have hInvLevi := inverseSquare_levi_abs_bound g u hu x (hu0 x) hULevi hU
  have hCross := scalarFirstCovector_cross_abs_bound g hf hInvSmooth x
    (by positivity : 0 < B*u x/v) (by positivity : 0 < 2*B/(u x)^3) hGrad hInvGrad
  have hError := hermAbsLE_add (hermAbsLE_real_smul hInvLevi (f x)) hCross
  have hCost : |f x| * ((2*B+6*B^2)/(u x)^4)+2*(B*u x/v)*(2*B/(u x)^3) ≤
      (B*(2*B+6*B^2)+4*B^2)/((u x)^2*v) := by
    calc
      _ ≤ (B*(u x)^2/v)*((2*B+6*B^2)/(u x)^4)+2*(B*u x/v)*(2*B/(u x)^3) :=
        add_le_add (mul_le_mul_of_nonneg_right hSize (by positivity)) le_rfl
      _ = _ := by field_simp <;> ring
  have hErrorBound := hermAbsLE_mono hG hError hCost
  have hMain := hermLE_real_smul hFLevi (show 0 ≤ 1/(u x)^2 from by positivity)
  have hTotal := hermLE_add hMain hErrorBound.1
  have hGrouping : levi (normalizedCorrection u f) x=
      Complex.ofReal (1/(u x)^2) • levi f x+
        (Complex.ofReal (f x) • levi (fun y => (u y)^(-2:ℤ)) x+
          (Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector (fun y => (u y)^(-2:ℤ)) x)+
           Matrix.vecMulVec (star (scalarFirstCovector (fun y => (u y)^(-2:ℤ)) x)) (scalarFirstCovector f x))) := by
    change levi (fun y => f y*(u y)^(-2:ℤ)) x=_
    rw [levi_real_mul hf hInvSmooth x,hInvValue]
    abel
  rw [hGrouping]
  convert hTotal using 1
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_div]
  have huC : (u x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu0 x).ne'
  have hvC : (v:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp
  <;> norm_num
  <;> ring

end Yau.Proofs.F03Aux
