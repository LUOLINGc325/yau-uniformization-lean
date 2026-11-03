import Yau.Proofs.D06Elementary

/-! Mean value for the original closed-disc regularity hypotheses. -/

open scoped Matrix ContDiff Ring Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem onCircle_periodic (H : ℂ → Matrix (Fin r) (Fin r) ℂ) :
    Function.Periodic (Yau.Blueprint.onCircle H) (2 * Real.pi) := by
  intro t
  apply congrArg H
  simpa only [circleMap_zero, Complex.ofReal_one, one_mul] using
    periodic_circleMap (0 : ℂ) 1 t

theorem onCircle_entry_smooth (H : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) (Metric.closedBall 0 1)) :
    ∀ i j, ContDiff ℝ ∞ (fun t => Yau.Blueprint.onCircle H t i j) := by
  intro i j
  have hcurve : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (t * Complex.I)) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  apply (hH i j).comp_contDiff hcurve
  intro t
  simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I, le_refl]

/-- The smooth inverse in the frozen contract is automatically holomorphic on
the open disc; this follows from the Banach-algebra inverse map. -/
theorem inverse_differentiableOn (H K : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (hd : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hHK : ∀ z ∈ Metric.ball (0 : ℂ) 1, H z * K z = 1 ∧ K z * H z = 1) :
    DifferentiableOn ℂ K (Metric.ball 0 1) := by
  have hunit : ∀ z ∈ Metric.ball (0 : ℂ) 1, IsUnit (H z) := by
    intro z hz
    exact isUnit_iff_exists.mpr ⟨K z, hHK z hz⟩
  apply (hd.inverse hunit).congr
  intro z hz
  calc
    K z = (H z)⁻¹ʳ * (H z * K z) :=
      (Ring.inverse_mul_cancel_left (H z) (K z) (hunit z hz)).symm
    _ = (H z)⁻¹ʳ := by rw [(hHK z hz).1, Matrix.mul_one]

/-- Holomorphicity on the open disc and continuity on the exact closed disc
already suffice for the normalized boundary mean. -/
theorem matrix_circle_mean (F : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (hd : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hc : ContinuousOn F (Metric.closedBall 0 1)) :
    (2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi),
      F (Complex.exp (t * Complex.I))) = F 0 := by
  have hf : DiffContOnCl ℂ F (Metric.ball (0 : ℂ) |(1 : ℝ)|) := by
    refine ⟨?_, ?_⟩
    · simpa only [abs_one] using hd
    · simpa only [abs_one, closure_ball _ one_ne_zero] using hc
  simpa only [Real.circleAverage, circleMap_zero, Complex.ofReal_one, one_mul] using
    DiffContOnCl.circleAverage (c := (0 : ℂ)) (R := (1 : ℝ)) hf

end Yau.NodeProofs.D06Aux
