import Yau.Proofs.F03NormalizedCorrection
import Yau.Proofs.F03GradientCoefficients

/-! Actual logarithmic gradient calculus for the existing comparison weight. -/
noncomputable section
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem comparisonLogWeight_gradient_bound (g : HermitianField M)
    (u f : M.Carrier → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) (hf : SmoothFn f)
    (A : ℝ) (hA : 0 ≤ A) (k : ℕ) (x : M.Carrier) {B v : ℝ} (hB : 0 < B) (hv : 0 < v)
    (hU : Real.sqrt (gradNormSq g u x) ≤ B) (hSize : |f x| ≤ B*(u x)^2/v)
    (hGrad : Real.sqrt (gradNormSq g f x) ≤ B*u x/v) :
    Real.sqrt (gradNormSq g (comparisonLogWeight u f A k) x) ≤
      ((k:ℝ)*B+A*(B+2*B^2)/v)/u x := by
  have hx0 : 0 < u x := hu0 x
  have hLog := smoothFn_log_of_pos u hu hu0
  have hQ := normalizedCorrection_smooth u f hu hu0 hf
  have hLeft : SmoothFn (fun y => -(k:ℝ)*Real.log (u y)) := fun a => contDiffOn_const.mul (hLog a)
  have hRight : SmoothFn (fun y => A*normalizedCorrection u f y) := fun a => contDiffOn_const.mul (hQ a)
  have hTriangle := sqrt_gradNormSq_sub_le g hLeft hRight x
  rw [sqrt_gradNormSq_const_mul g hLog,sqrt_gradNormSq_const_mul g hQ,
    sqrt_gradNormSq_log g u hu hu0 x,abs_neg,abs_of_nonneg (Nat.cast_nonneg k),abs_of_nonneg hA] at hTriangle
  apply hTriangle.trans
  calc
    _ ≤ (k:ℝ)*((1/u x)*B)+A*((B+2*B^2)/(u x*v)) := add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU (by positivity)) (Nat.cast_nonneg k))
      (mul_le_mul_of_nonneg_left (normalizedCorrection_gradient_bound g u f hu hu0 hf x hB hv hU hSize hGrad) hA)
    _ = _ := by ring

theorem comparisonWeight_gradient_bound (g : HermitianField M)
    (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ) (hu : SmoothFn u) (hu0 : ∀ x,0 < u x)
    (A : ℝ) (hA : 0 ≤ A) (k : ℕ) (t : ℝ) (hH : SmoothFn (fun y => H y t))
    (x : M.Carrier) {B v : ℝ} (hB : 0 < B) (hv : 1 ≤ v)
    (hU : Real.sqrt (gradNormSq g u x) ≤ B) (hSize : |H x t| ≤ B*(u x)^2/v)
    (hGrad : Real.sqrt (gradNormSq g (fun y => H y t) x) ≤ B*u x/v) :
    gradNormSq g (fun y => comparisonWeight u H A k y t) x ≤
      ((1+(k:ℝ)*B+A*(B+2*B^2))*comparisonWeight u H A k x t/u x)^2 := by
  have hx0 : 0 < u x := hu0 x
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  let f := comparisonLogWeight u (fun y => H y t) A k
  have hf : SmoothFn f := comparisonLogWeight_smooth u _ hu hu0 hH A k
  have hEq : (fun y => comparisonWeight u H A k y t)=(fun y => Real.exp (f y)) :=
    funext (fun y => comparisonWeight_eq_exp_logWeight u H A k y t (hu0 y))
  have hSmooth : SmoothFn (fun y => comparisonWeight u H A k y t) := by
    rw [hEq]
    exact fun a => (hf a).exp
  have hLog := comparisonLogWeight_gradient_bound g u (fun y => H y t) hu hu0 hH A hA k x hB hv0 hU hSize hGrad
  have hCoeff : ((k:ℝ)*B+A*(B+2*B^2)/v)/u x ≤ (1+(k:ℝ)*B+A*(B+2*B^2))/u x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    have hh : A*(B+2*B^2)/v ≤ A*(B+2*B^2) := div_le_self (by positivity) hv
    linarith
  have hSqrt : Real.sqrt (gradNormSq g (fun y => comparisonWeight u H A k y t) x) ≤
      (1+(k:ℝ)*B+A*(B+2*B^2))*comparisonWeight u H A k x t/u x := by
    rw [hEq,sqrt_gradNormSq_scalar_comp g hf Real.exp Real.contDiff_exp x,Real.deriv_exp,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (f x)*((1+(k:ℝ)*B+A*(B+2*B^2))/u x) :=
        mul_le_mul_of_nonneg_left (hLog.trans hCoeff) (Real.exp_pos _).le
      _ = _ := by rw [comparisonWeight_eq_exp_logWeight u H A k x t hx0];dsimp [f];ring
  have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hSqrt 2
  rw [Real.sq_sqrt (smooth_gradNormSq_nonneg g hSmooth x)] at hSq
  exact hSq

end Yau.Proofs.F03Aux
