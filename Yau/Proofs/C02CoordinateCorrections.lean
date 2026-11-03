import Yau.Proofs.C02AffinePositiveJets
import Yau.Proofs.C02MultilinearOutputBounds

/-! Scalar coordinate corrections of the one chosen vector map retain
its derivative closeness and recover all its positive-order vector jets. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

def coordinateCorrection (F : ComplexVector n → ComplexVector n) (k : Fin n)
    (x : ComplexVector n) : ℂ := x k - F x k

theorem coordinateCorrection_contDiff (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F) (k : Fin n) : ContDiff ℝ ∞ (coordinateCorrection F k) := by
  let pr := (EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ
  have h := pr.contDiff.comp (contDiff_id.sub hF)
  exact h

theorem coordinate_projection_norm_le_one (k : Fin n) :
    ‖(EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  exact (PiLp.norm_apply_le v k).trans_eq (one_mul _).symm

theorem coordinateCorrection_fderiv_norm_le
    {F : ComplexVector n → ComplexVector n} {x : ComplexVector n}
    (hF : DifferentiableAt ℝ F x) (k : Fin n) :
    ‖fderiv ℝ (coordinateCorrection F k) x‖ ≤
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ := by
  let pr := (EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ
  have hD : HasFDerivAt (coordinateCorrection F k)
      (pr.comp (ContinuousLinearMap.id ℝ (ComplexVector n) - fderiv ℝ F x)) x :=
    pr.hasFDerivAt.comp x ((hasFDerivAt_id x).sub hF.hasFDerivAt)
  rw [hD.fderiv]
  calc
    _ ≤ ‖pr‖ * ‖ContinuousLinearMap.id ℝ (ComplexVector n) - fderiv ℝ F x‖ := pr.opNorm_comp_le _
    _ ≤ 1 * ‖ContinuousLinearMap.id ℝ (ComplexVector n) - fderiv ℝ F x‖ :=
      mul_le_mul_of_nonneg_right (coordinate_projection_norm_le_one k) (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_sub_rev]

theorem coordinate_map_positive_jet_bound_of_corrections
    (F : ComplexVector n → ComplexVector n) (hF : ContDiff ℝ ∞ F)
    (m : ℕ) (hm : 1 ≤ m) (x : ComplexVector n) (B : ℝ)
    (hBound : ∀ k : Fin n, ‖iteratedFDeriv ℝ m (coordinateCorrection F k) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ (n : ℝ) * (1 + B) := by
  apply (norm_iteratedFDeriv_le_sum_complex_coordinates F hF m x).trans
  calc
    _ ≤ ∑ _k : Fin n, (1 + B) := by
      apply Finset.sum_le_sum
      intro k _
      let pr := (EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ
      have hEq : (fun y => F y k) = fun y => pr y - coordinateCorrection F k y := by
        funext y
        change F y k = y k - (y k - F y k)
        abel
      rw [hEq, fun_iteratedFDeriv_sub_apply (pr.contDiff.contDiffAt.of_le (by simp : (m : ℕ∞ω) ≤ ∞))
        ((coordinateCorrection_contDiff F hF k).contDiffAt.of_le (by simp : (m : ℕ∞ω) ≤ ∞))]
      apply (norm_sub_le _ _).trans
      apply add_le_add _ (hBound k)
      simpa only [zero_add] using (norm_iteratedFDeriv_affine_pos_le (0 : ℂ) pr m hm x).trans
        (coordinate_projection_norm_le_one k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Yau.Blueprint.C02Proof
