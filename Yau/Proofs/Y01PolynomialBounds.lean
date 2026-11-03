import Yau.Proofs.Y01JetNormExtraction
import Yau.Proofs.U02AnalyticBounds

/-! On the unit ball polynomial evaluation is bounded by its literal
coefficient norm. The established Cauchy estimate then bounds every fixed jet. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n : ℕ}

theorem scalar_eval_norm_le_coeffNorm (p : MvPolynomial (Fin n) ℂ)
    {z : ComplexVector n} (hz : ‖z‖ ≤ 1) : ‖polyEval p z‖ ≤ polynomialCoeffNorm p := by
  classical
  unfold polyEval
  rw [eval_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  have hprod : ‖∏ i ∈ a.support, z i ^ a i‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ((PiLp.norm_apply_le z i).trans hz)
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans_eq (mul_one _)

theorem vector_norm_le_sum_coordinates (z : ComplexVector n) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  have heq : (∑ i, z i • stdVec i) = z := by
    ext j
    simp [stdVec, Pi.single_apply]
  calc
    ‖z‖ = ‖∑ i, z i • stdVec i‖ := congrArg norm heq.symm
    _ ≤ ∑ i, ‖z i • stdVec i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, stdVec_norm, mul_one]

theorem polyMap_eval_norm_le_coeffNorm (P : PolyMap n)
    {z : ComplexVector n} (hz : ‖z‖ ≤ 1) : ‖P.eval z‖ ≤ P.coeffNorm := by
  apply (vector_norm_le_sum_coordinates (P.eval z)).trans
  change (∑ i, ‖polyEval (P i) z‖) ≤ ∑ i, polynomialCoeffNorm (P i)
  exact Finset.sum_le_sum (fun i hi => scalar_eval_norm_le_coeffNorm (P i) hz)

def cauchyJetConstant (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), (2 * ((m : ℝ) + 1)) ^ m

theorem jetNorm_eval_le_coeffNorm (P : PolyMap n) (d : ℕ) :
    jetNorm P.eval d ≤ cauchyJetConstant d * P.coeffNorm := by
  have hbound (m : ℕ) : ‖iteratedFDeriv ℂ m P.eval 0‖ ≤
      P.coeffNorm * (2 * ((m : ℝ) + 1)) ^ m := by
    have h := U02AnalyticAux.norm_iteratedFDeriv_center_le (f := P.eval) (x := 0)
      (R := 1) zero_lt_one (coeffNorm_nonneg P) (polyMap_eval_contDiff P).contDiffOn
      (fun z hz => polyMap_eval_norm_le_coeffNorm P
        (by
          have hnorm : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
          exact hnorm.le)) m
    simpa only [div_one] using h
  unfold jetNorm cauchyJetConstant
  calc
    _ ≤ ∑ m ∈ Finset.range (d + 1), P.coeffNorm * (2 * ((m : ℝ) + 1)) ^ m :=
      Finset.sum_le_sum (fun m hm => hbound m)
    _ = _ := by rw [← Finset.mul_sum]; ring

end Yau.Proofs.Y01Aux
