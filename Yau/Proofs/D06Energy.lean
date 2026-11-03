import Yau.Proofs.D06TraceEstimates
import Yau.Proofs.D06CircleMean

/-! The normalized relative factor and its mean, as used in the source's
symmetric translation energy argument. -/

open scoped Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

variable {r : ℕ}

theorem frobSq_sub_one (A : Matrix (Fin r) (Fin r) ℂ) :
    frobSq (A - 1) = frobSq A - 2 * (Matrix.trace A).re + r := by
  have hmul : (A - 1)ᴴ * (A - 1) = Aᴴ * A - Aᴴ - A + 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    noncomm_ring
  rw [frobSq_eq_re_trace, hmul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_conjTranspose]
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re,
    Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, ← frobSq_eq_re_trace]
  ring

theorem frobSq_mul_eq_re_trace_gram (H K : Matrix (Fin r) (Fin r) ℂ) :
    frobSq (H * K) = (Matrix.trace ((Hᴴ * H) * (K * Kᴴ))).re := by
  rw [frobSq_eq_re_trace, Matrix.conjTranspose_mul]
  congr 1
  calc
    _ = Matrix.trace (Kᴴ * ((Hᴴ * H) * K)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((Hᴴ * H) * K) * Kᴴ) := Matrix.trace_mul_comm _ _
    _ = _ := by rw [Matrix.mul_assoc]

def relativeFactor (H K : ℂ → Matrix (Fin r) (Fin r) ℂ) (θ : ℝ) :
    ℂ → Matrix (Fin r) (Fin r) ℂ :=
  fun z => H (Complex.exp (θ * Complex.I) * z) * K z

theorem relativeFactor_differentiableOn (H K : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (θ : ℝ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hK : DifferentiableOn ℂ K (Metric.ball 0 1)) :
    DifferentiableOn ℂ (relativeFactor H K θ) (Metric.ball 0 1) := by
  have hrot : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (θ * Complex.I) * z)
      (Metric.ball 0 1) := by fun_prop
  apply (hH.comp hrot ?_).mul hK
  intro z hz
  simpa only [Metric.mem_ball, dist_zero_right, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul] using hz

theorem relativeFactor_continuousOn (H K : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (θ : ℝ) (hH : ContinuousOn H (Metric.closedBall 0 1))
    (hK : ContinuousOn K (Metric.closedBall 0 1)) :
    ContinuousOn (relativeFactor H K θ) (Metric.closedBall 0 1) := by
  have hrot : ContinuousOn (fun z : ℂ => Complex.exp (θ * Complex.I) * z)
      (Metric.closedBall 0 1) := by fun_prop
  apply (hH.comp hrot ?_).mul hK
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul] using hz

theorem relativeFactor_mean (H K : ℂ → Matrix (Fin r) (Fin r) ℂ) (θ : ℝ)
    (hHd : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hKd : DifferentiableOn ℂ K (Metric.ball 0 1))
    (hHc : ContinuousOn H (Metric.closedBall 0 1))
    (hKc : ContinuousOn K (Metric.closedBall 0 1)) (h0 : H 0 * K 0 = 1) :
    (2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi),
      relativeFactor H K θ (Complex.exp (t * Complex.I))) = 1 := by
  rw [matrix_circle_mean _ (relativeFactor_differentiableOn H K θ hHd hKd)
    (relativeFactor_continuousOn H K θ hHc hKc)]
  simpa only [relativeFactor, mul_zero] using h0

end Yau.NodeProofs.D06Aux
