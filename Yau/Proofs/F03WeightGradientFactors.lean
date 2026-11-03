import Yau.Proofs.F03WeightScalarCalculus
import Yau.Proofs.F03LeviGradientBounds

/-! Exact physical gradient factors and actual two-sided Levi bounds for log u and u^-2. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem sqrt_gradNormSq_log (g : HermitianField M) (u : M.Carrier → ℝ)
    (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => Real.log (u y)) x)=
      (1/u x)*Real.sqrt (gradNormSq g u x) := by
  rw [sqrt_gradNormSq_scalar_comp_at g hu Real.log (smoothFn_log_of_pos u hu hu0) x
    (Real.differentiableAt_log (hu0 x).ne'),Real.deriv_log,abs_of_pos (inv_pos.mpr (hu0 x))]
  simp only [one_div]

theorem sqrt_gradNormSq_inverseSquare (g : HermitianField M) (u : M.Carrier → ℝ)
    (hu : SmoothFn u) (hu0 : ∀ x,0 < u x) (x : M.Carrier) :
    Real.sqrt (gradNormSq g (fun y => (u y)^(-2:ℤ)) x)=
      (2/(u x)^3)*Real.sqrt (gradNormSq g u x) := by
  rw [sqrt_gradNormSq_scalar_comp_at g hu _ (smoothFn_inverseSquare_of_pos u hu hu0) x
    (differentiableAt_zpow.mpr (Or.inl (hu0 x).ne')),inverseSquare_deriv]
  rw [abs_div,abs_of_pos (pow_pos (hu0 x) 3)]
  norm_num

theorem log_levi_abs_bound (g : HermitianField M) (u : M.Carrier → ℝ)
    (hu : SmoothFn u) (x : M.Carrier) (hu0 : 0 < u x) {B : ℝ}
    (hU : HermAbsLE (levi u x) (gMat g x) (B/u x))
    (hGrad : Real.sqrt (gradNormSq g u x) ≤ B) :
    HermAbsLE (levi (fun y => Real.log (u y)) x) (gMat g x) ((B+B^2)/(u x)^2) := by
  have hOuter := scalarFirstCovector_abs_bound g hu x hGrad
  have hBoth := hermAbsLE_add (hermAbsLE_real_smul hU (1/u x))
    (hermAbsLE_real_smul hOuter (-1/(u x)^2))
  have hCoeff : |1/u x| *(B/u x)+|-1/(u x)^2| *B^2=(B+B^2)/(u x)^2 := by
    rw [abs_of_pos (div_pos zero_lt_one hu0),abs_div,abs_of_pos (sq_pos_of_pos hu0)]
    norm_num
    field_simp
    <;> ring
  rw [levi_log_of_pos u hu x hu0]
  rw [hCoeff] at hBoth
  simpa only [Complex.ofReal_neg,neg_smul,sub_eq_add_neg,neg_div] using hBoth

theorem inverseSquare_levi_abs_bound (g : HermitianField M) (u : M.Carrier → ℝ)
    (hu : SmoothFn u) (x : M.Carrier) (hu0 : 0 < u x) {B : ℝ}
    (hU : HermAbsLE (levi u x) (gMat g x) (B/u x))
    (hGrad : Real.sqrt (gradNormSq g u x) ≤ B) :
    HermAbsLE (levi (fun y => (u y)^(-2:ℤ)) x) (gMat g x)
      ((2*B+6*B^2)/(u x)^4) := by
  have hOuter := scalarFirstCovector_abs_bound g hu x hGrad
  have hBoth := hermAbsLE_add (hermAbsLE_real_smul hU (-2/(u x)^3))
    (hermAbsLE_real_smul hOuter (6/(u x)^4))
  have hCoeff : |-2/(u x)^3| *(B/u x)+|6/(u x)^4| *B^2=(2*B+6*B^2)/(u x)^4 := by
    rw [abs_div,abs_div,abs_of_pos (pow_pos hu0 3),abs_of_pos (pow_pos hu0 4)]
    norm_num
    field_simp
    <;> ring
  rw [levi_inverseSquare_of_pos u hu x hu0]
  simpa only [hCoeff] using hBoth

end Yau.Proofs.F03Aux
