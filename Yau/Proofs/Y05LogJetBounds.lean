import Yau.Proofs.Y05BoundedRealPart
import Yau.Proofs.Y05TaylorBounds
import Yau.Proofs.U02AnalyticSeries
import Yau.Proofs.V03HolomorphicSmooth

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Yau.Proofs.Y02Aux MvPolynomial
open scoped ContDiff BigOperators

variable {n : ℕ}

def logJetConstant (n d : ℕ) (r : ℝ) : ℝ :=
  2 * scalarTaylorConstant n d *
    ∑ m ∈ Finset.range (d + 1), (2 * ((m : ℝ) + 1) / (r / 2)) ^ m

theorem logJetConstant_pos (n d : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < logJetConstant n d r := by
  have hsum : 0 < ∑ m ∈ Finset.range (d + 1),
      (2 * ((m : ℝ) + 1) / (r / 2)) ^ m := by
    apply Finset.sum_pos'
    · intro m _; positivity
    · exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
  have hC : 0 < scalarTaylorConstant n d := by
    unfold scalarTaylorConstant
    apply Finset.sum_pos'
    · intro m _; positivity
    · exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
  exact mul_pos (mul_pos (by norm_num) hC) hsum

/-- Borel--Carathéodory followed by the fixed-order Cauchy estimates controls
the actual Taylor polynomial linearly in the real-part bound. -/
theorem exists_scalar_taylor_bound_of_boundedRe {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    {P : ComplexVector n → ℂ} (hP : DifferentiableOn ℂ P (Metric.ball 0 r))
    (hP0 : P 0 = 0) (hRe : ∀ z ∈ Metric.ball (0 : ComplexVector n) r, (P z).re ≤ M)
    (d : ℕ) : ∃ B : MvPolynomial (Fin n) ℂ,
      B.totalDegree ≤ d ∧ B.coeff 0 = 0 ∧ ScalarJetEq (scalarEval B) P d ∧
        polynomialCoeffNorm B ≤ logJetConstant n d r * M := by
  have hr2 : 0 < r / 2 := by positivity
  have hsmall : DifferentiableOn ℂ P (Metric.ball 0 (r / 2)) :=
    hP.mono (Metric.ball_subset_ball (by linarith))
  have hC := Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn Metric.isOpen_ball hsmall
  have hb := boundedRe_norm_on_half_ball hr hM hP hP0 hRe
  have hp := (U02AnalyticAux.hasFPowerSeriesOnBall_of_complex_contDiffOn_infty hr2
    (by positivity : 0 ≤ 2 * M) hC hb).hasFPowerSeriesAt
  let B := taylorPolynomial (U02AnalyticAux.complexTaylorSeries P 0) d
  have hjet : ScalarJetEq (scalarEval B) P d := scalarJetEq_taylorPolynomial hp d
  refine ⟨B, taylorPolynomial_degree _ _, (coefficient_zero_of_scalarJetEq hjet).trans hP0,
    hjet, ?_⟩
  apply (coefficientNorm_canonical_taylor P d).trans
  have hnorm : scalarJetNorm P d ≤ (2 * M) *
      ∑ m ∈ Finset.range (d + 1), (2 * ((m : ℝ) + 1) / (r / 2)) ^ m := by
    rw [scalarJetNorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ =>
      U02AnalyticAux.norm_iteratedFDeriv_center_le hr2 (by positivity) hC hb m
  calc
    scalarTaylorConstant n d * scalarJetNorm P d ≤
        scalarTaylorConstant n d * ((2 * M) *
          ∑ m ∈ Finset.range (d + 1), (2 * ((m : ℝ) + 1) / (r / 2)) ^ m) :=
      mul_le_mul_of_nonneg_left hnorm (Finset.sum_nonneg fun m _ => by positivity)
    _ = logJetConstant n d r * M := by unfold logJetConstant; ring

end Yau.Proofs.Y05Aux
