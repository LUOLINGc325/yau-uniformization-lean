import Yau.Proofs.D05BoundaryDeterminant
import Yau.Proofs.D05FrobeniusAlgebra
import Yau.Proofs.V03DiscLaplacianGreen
import Yau.Proofs.V03HolomorphicNormLaplacian
import Yau.Proofs.V03VectorAreaFourier

/-! Green's formula for a normalized complex Gram matrix, with the exact
half-Laplacian and normalized Fourier constants on the original closed disc. -/

open scoped Topology ContDiff Matrix
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.D05Proof
open V03Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem complex_det_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℂ} {S : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) S) :
    ContDiffOn ℝ ∞ (fun z => (A z).det) S := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem complex_trace_re_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix ι ι ℂ} {S : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) S) :
    ContDiffOn ℝ ∞ (fun z => (Matrix.trace (A z)).re) S := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  simp only [Matrix.trace, Matrix.diag_apply]
  exact ContDiffOn.sum fun i _ => hA i i

theorem gram_green_logdet_eq_trace {Q : ℂ → Matrix ι ι ℂ}
    (hQ : ∀ i j, ContDiffOn ℝ ∞ (fun z => Q z i j) (Metric.closedBall (0 : ℂ) 1))
    (hdet : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Q z).det.re ≠ 0)
    (hcircle : ∀ θ : ℝ, Q (circlePoint θ) = 1) :
    (∫ z in Metric.ball (0 : ℂ) 1, closedLaplacian (fun w => Real.log (Q w).det.re) z) =
      ∫ z in Metric.ball (0 : ℂ) 1, closedLaplacian (fun w => (Matrix.trace (Q w)).re) z := by
  have hlog : ContDiffOn ℝ ∞ (fun w => Real.log (Q w).det.re)
      (Metric.closedBall (0 : ℂ) 1) :=
    (Complex.reCLM.contDiff.comp_contDiffOn (complex_det_contDiffOn hQ)).log hdet
  rw [integral_closedLaplacian_eq_boundary hlog,
    integral_closedLaplacian_eq_boundary (complex_trace_re_contDiffOn hQ)]
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact gram_logdet_boundary_normal_eq_trace
    (uniqueDiffOn_real_closedDisc (circlePoint θ) (circlePoint_mem_closedBall θ))
    (fun i j => (hQ i j).differentiableOn (by simp) _ (circlePoint_mem_closedBall θ))
    (hcircle θ) (circlePoint θ)

theorem normDiscArea_eq_half_laplacian_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {f : ℂ → H}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    normDiscArea f = ENNReal.ofReal ((1 / 2 : ℝ) *
      ∫ z in Metric.ball (0 : ℂ) 1, closedLaplacian (fun w => ‖f w‖ ^ 2) z) := by
  have hreal : (∫ z in Metric.ball (0 : ℂ) 1, 2 * ‖closedDiscDerivative f z‖ ^ 2) =
      (1 / 2 : ℝ) * ∫ z in Metric.ball (0 : ℂ) 1,
        closedLaplacian (fun w => ‖f w‖ ^ 2) z := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ nhds z :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
    rw [closedLaplacian_holomorphic_norm_sq hz ((hf.contDiffAt hnhds).of_le (by simp)),
      closedDiscDerivative, fderivWithin_of_mem_nhds hnhds]
    ring
  have ha := normDiscArea_radial_eq_integral hf (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul, radialEuclideanDensity, one_smul] at ha
  exact ha.trans (congrArg ENNReal.ofReal hreal)

def flattenMatrixDisc (U : ℂ → Matrix κ ι ℂ) (z : ℂ) : EuclideanSpace ℂ (κ × ι) :=
  WithLp.toLp 2 (fun p => U z p.1 p.2)

theorem flattenMatrixDisc_contDiffOn {U : ℂ → Matrix κ ι ℂ} {S : Set ℂ}
    (hU : ∀ i j, ContDiffOn ℂ ∞ (fun z => U z i j) S) :
    ContDiffOn ℂ ∞ (flattenMatrixDisc U) S :=
  (contDiffOn_piLp 2).mpr fun p => hU p.1 p.2

theorem gramEntry_contDiffOn {U : ℂ → Matrix κ ι ℂ} {S : Set ℂ}
    (hU : ∀ i j, ContDiffOn ℂ ∞ (fun z => U z i j) S) (i j : ι) :
    ContDiffOn ℝ ∞ (fun z => ((U z)ᴴ * U z) i j) S := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffOn.sum fun k _ =>
    (Complex.conjCLE.contDiff.comp_contDiffOn ((hU k i).restrict_scalars ℝ)).mul
      ((hU k j).restrict_scalars ℝ)

theorem normalized_gram_half_laplacian_area {U : ℂ → Matrix κ ι ℂ}
    (hU : ∀ i j, ContDiffOn ℂ ∞ (fun z => U z i j) (Metric.closedBall (0 : ℂ) 1))
    (hdet : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ((U z)ᴴ * U z).det.re ≠ 0)
    (hcircle : ∀ θ : ℝ, (U (circlePoint θ))ᴴ * U (circlePoint θ) = 1) :
    normDiscArea (flattenMatrixDisc U) = ENNReal.ofReal ((1 / 2 : ℝ) *
      ∫ z in Metric.ball (0 : ℂ) 1,
        closedLaplacian (fun w => Real.log ((U w)ᴴ * U w).det.re) z) := by
  have ht : (fun z => (Matrix.trace ((U z)ᴴ * U z)).re) =
      fun z => ‖flattenMatrixDisc U z‖ ^ 2 := by
    funext z
    exact (matrixFrobSq_eq_trace (U z)).symm.trans (matrixFrobSq_eq_flatten_norm_sq (U z))
  have hg := gram_green_logdet_eq_trace (gramEntry_contDiffOn hU) hdet hcircle
  rw [ht] at hg
  rw [normDiscArea_eq_half_laplacian_norm (flattenMatrixDisc_contDiffOn hU), hg]

theorem normalized_gram_fourier {U : ℂ → Matrix κ ι ℂ}
    (hU : ∀ i j, ContDiffOn ℂ ∞ (fun z => U z i j) (Metric.closedBall (0 : ℂ) 1))
    (hdet : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ((U z)ᴴ * U z).det.re ≠ 0)
    (hcircle : ∀ θ : ℝ, (U (circlePoint θ))ᴴ * U (circlePoint θ) = 1) :
    matrixDSq (fun θ => U (circlePoint θ)) = ENNReal.ofReal
      (((1 / 2 : ℝ) * ∫ z in Metric.ball (0 : ℂ) 1,
        closedLaplacian (fun w => Real.log ((U w)ᴴ * U w).det.re) z) / (2 * Real.pi)) := by
  change boundaryDSq (fun θ p => flattenMatrixDisc U (circlePoint θ) p) = _
  rw [boundaryDSq_vector_eq_inverse_area (flattenMatrixDisc_contDiffOn hU),
    normalized_gram_half_laplacian_area hU hdet hcircle,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
  congr 1
  ring

end Yau.Blueprint.D05Proof
