import Yau.Proofs.F03ComparisonWeightGradient
import Yau.Proofs.F03ComparisonWeightNumerics

/-! The actual comparison-weight Levi matrix has the negative metric-defect term and a decaying error. -/
noncomputable section
open scoped ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

def weightBaseError (B : ℝ) (k : ℕ) : ℝ := (k:ℝ)*(B+B^2)+2*((k:ℝ)*B)^2
def weightDecayError (B A : ℝ) : ℝ := A*(B+6*B^2+6*B^3)+2*(A*(B+2*B^2))^2

theorem comparisonWeight_hessian_bound (g : HermitianField M)
    (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x)
    (A : ℝ) (hA : 0 ≤ A) (k : ℕ) (t : ℝ) (hH : SmoothFn (fun y => H y t))
    (x : M.Carrier) (D : Herm n) {B v : ℝ} (hB : 0 < B) (hv : 1 ≤ v)
    (hU : Real.sqrt (gradNormSq g u x) ≤ B)
    (hULevi : HermAbsLE (levi u x) (gMat g x) (B/u x))
    (hSize : |H x t| ≤ B*(u x)^2/v)
    (hGrad : Real.sqrt (gradNormSq g (fun y => H y t) x) ≤ B*u x/v)
    (hHLevi : HermLE (D-Complex.ofReal (B/v) • gMat g x) (levi (fun y => H y t) x)) :
    HermLE (levi (fun y => comparisonWeight u H A k y t) x)
      (Complex.ofReal (comparisonWeight u H A k x t/(u x)^2) •
        (Complex.ofReal (-A) • D+
          Complex.ofReal (weightBaseError B k+weightDecayError B A/v) • gMat g x)) := by
  have hx0 : 0 < u x := hu0 x
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hG : (gMat g x).PosSemidef := (hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  let f := comparisonLogWeight u (fun y => H y t) A k
  let q := normalizedCorrection u (fun y => H y t)
  have hf : SmoothFn f := comparisonLogWeight_smooth u _ hu hu0 hH A k
  have hq : SmoothFn q := normalizedCorrection_smooth u _ hu hu0 hH
  have hLog := smoothFn_log_of_pos u hu hu0
  have hLogAbs := log_levi_abs_bound g u hu x hx0 hULevi hU
  have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hNegativeLog : HermLE (Complex.ofReal (-(k:ℝ)) • levi (fun y => Real.log (u y)) x)
      (Complex.ofReal ((k:ℝ)*(B+B^2)/(u x)^2) • gMat g x) := by
    simpa only [abs_neg,abs_of_nonneg hk0,mul_div_assoc] using
      (hermAbsLE_real_smul hLogAbs (-(k:ℝ))).2
  have hQLower := normalizedCorrection_levi_lower_bound g u (fun y => H y t) hu hu0 hH x D hB hv0 hU hULevi hSize hGrad hHLevi
  have hNegativeQ := hermLE_neg (hermLE_real_smul hQLower hA)
  have hNegativeQ' : HermLE (Complex.ofReal (-A) • levi q x)
      (-(Complex.ofReal A • (Complex.ofReal (1/(u x)^2) •
        (D-Complex.ofReal ((B+6*B^2+6*B^3)/v) • gMat g x)))) := by
    simpa only [Complex.ofReal_neg,neg_smul] using hNegativeQ
  have hIdentity : levi f x=Complex.ofReal (-(k:ℝ)) • levi (fun y => Real.log (u y)) x+
      Complex.ofReal (-A) • levi q x := by
    have hEq : f=(fun y => -(k:ℝ)*Real.log (u y)+(-A)*q y) := by
      funext y
      dsimp [f,q,comparisonLogWeight,normalizedCorrection]
      ring
    rw [hEq,levi_real_add (fun a => contDiffOn_const.mul (hLog a))
      (fun a => contDiffOn_const.mul (hq a)),levi_real_const_mul hLog,levi_real_const_mul hq]
  have hLogUpper : HermLE (levi f x)
      (Complex.ofReal (1/(u x)^2) •
        (Complex.ofReal (-A) • D+
          Complex.ofReal ((k:ℝ)*(B+B^2)+A*(B+6*B^2+6*B^3)/v) • gMat g x)) := by
    rw [hIdentity]
    convert hermLE_add hNegativeLog hNegativeQ' using 1
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_neg]
    norm_num
    ring
  have hGradient := comparisonLogWeight_gradient_bound g u (fun y => H y t) hu hu0 hH A hA k x hB hv0 hU hSize hGrad
  have hOuter := scalarFirstCovector_abs_bound g hf x hGradient
  have hOuterUpper := (hermAbsLE_mono hG hOuter
    (weight_gradient_square_bound (a := (k:ℝ)*B) (b := A*(B+2*B^2)) hx0 hv)).2
  have hInner := hermLE_add hLogUpper hOuterUpper
  have hExpUpper := hermLE_real_smul hInner (Real.exp_pos (f x)).le
  have hEq : (fun y => comparisonWeight u H A k y t)=(fun y => Real.exp (f y)) :=
    funext (fun y => comparisonWeight_eq_exp_logWeight u H A k y t (hu0 y))
  rw [hEq,levi_real_scalar_comp hf Real.exp Real.contDiff_exp x]
  simp only [Real.deriv_exp]
  rw [← smul_add]
  convert hExpUpper using 1
  ext i j
  simp only [weightBaseError,weightDecayError,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_neg,comparisonWeight_eq_exp_logWeight u H A k x t hx0]
  dsimp only [f]
  norm_num
  ring

end Yau.Proofs.F03Aux
