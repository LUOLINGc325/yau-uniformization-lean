import Yau.Proofs.D06OriginalSourceInputs
import Yau.Proofs.D06CircleSeminormTransport

/-! Once the original canonical factors have their actual closed-disc jets,
all boundary identities and sharp original seminorm estimates follow for those
same factors. No alternative factor or extension is introduced. -/

open scoped Matrix Matrix.Norms.L2Operator ContDiff
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux
namespace BoundarySource

open Yau.Blueprint
variable {r : ℕ} (s : BoundarySource r)

def Hcircle (t : HardyCircle) : Matrix (Fin r) (Fin r) ℂ := s.H (fourier 1 t)
def Pcircle (t : HardyCircle) : Matrix (Fin r) (Fin r) ℂ := s.Hinv (fourier 1 t)

theorem Hcircle_coe (θ : ℝ) : s.Hcircle (θ : HardyCircle) = onCircle s.H θ := by
  have h := hardy_fourier_coe_exp 1 θ
  simpa only [Hcircle, onCircle, Nat.cast_one, mul_one] using congrArg s.H h

theorem Pcircle_coe (θ : ℝ) : s.Pcircle (θ : HardyCircle) = onCircle s.Hinv θ := by
  have h := hardy_fourier_coe_exp 1 θ
  simpa only [Pcircle, onCircle, Nat.cast_one, mul_one] using congrArg s.Hinv h

theorem Hcircle_trace_ae : s.Hcircle =ᵐ[hardyCircleMeasure]
    hardyQTrace s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper :=
  hardyMatrixInterior_circle_ae s.qColumns (fun i j => (s.pair_firstSobolev i j).1)

theorem Pcircle_trace_ae : s.Pcircle =ᵐ[hardyCircleMeasure]
    hardyPTrace s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper :=
  hardyMatrixInterior_circle_ae s.pColumns (fun i j => (s.pair_firstSobolev i j).2)

theorem Hcircle_continuous (hc : ContinuousOn s.H (Metric.closedBall 0 1)) : Continuous s.Hcircle := by
  exact hc.comp_continuous (fourier 1).continuous (fun t => by
    simp only [Metric.mem_closedBall, dist_zero_right, fourier_apply, Circle.norm_coe, le_refl])

theorem Pcircle_continuous (hc : ContinuousOn s.Hinv (Metric.closedBall 0 1)) : Continuous s.Pcircle := by
  exact hc.comp_continuous (fourier 1).continuous (fun t => by
    simp only [Metric.mem_closedBall, dist_zero_right, fourier_apply, Circle.norm_coe, le_refl])

theorem closed_inverse
    (hH : ContinuousOn s.H (Metric.closedBall 0 1))
    (hP : ContinuousOn s.Hinv (Metric.closedBall 0 1)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, s.H z * s.Hinv z = 1 ∧ s.Hinv z * s.H z = 1 := by
  have hHP : Set.EqOn (fun z => s.H z * s.Hinv z) (fun _ => 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact hardyQ_mul_P s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper z
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have hPH : Set.EqOn (fun z => s.Hinv z * s.H z) (fun _ => 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact hardyP_mul_Q s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper z
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have hdense : Metric.closedBall (0 : ℂ) 1 ⊆ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  have h1 := hHP.of_subset_closure (hH.mul hP) continuousOn_const Metric.ball_subset_closedBall hdense
  have h2 := hPH.of_subset_closure (hP.mul hH) continuousOn_const Metric.ball_subset_closedBall hdense
  intro z hz
  exact ⟨h1 hz, h2 hz⟩

theorem boundary_factor (hH : ContinuousOn s.H (Metric.closedBall 0 1)) :
    ∀ θ : ℝ, s.L θ = (onCircle s.H θ)ᴴ * onCircle s.H θ := by
  have hAE : s.symbol =ᵐ[hardyCircleMeasure] fun t => (s.Hcircle t)ᴴ * s.Hcircle t := by
    filter_upwards [s.Hcircle_trace_ae,
      hardyQTrace_factor s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper]
      with t ht hf
    rw [ht]
    exact hf
  have hc := s.Hcircle_continuous hH
  have heq := Measure.eq_of_ae_eq hAE s.symbol_continuous (hc.matrix_conjTranspose.mul hc)
  intro θ
  have h := congrFun heq (θ : HardyCircle)
  simpa only [symbol, periodicSymbol_coe, Hcircle_coe] using h

theorem sharp_seminorms
    (hH : ContinuousOn s.H (Metric.closedBall 0 1))
    (hP : ContinuousOn s.Hinv (Metric.closedBall 0 1)) :
    halfSobolevSq (onCircle s.H) ≤ ENNReal.ofReal (s.M / (2 * s.m ^ 2)) * halfSobolevSq s.L ∧
      halfSobolevSq (onCircle s.Hinv) ≤ ENNReal.ofReal (1 / (2 * s.m ^ 3)) * halfSobolevSq s.L := by
  have hm : 0 < s.m := s.m_pos
  have hM : 0 ≤ s.M := s.M_nonneg
  have hHD (θ : HardyCircle) : circleDifference s.Hcircle θ ≤
      s.M / (2 * s.m ^ 2) * circleDifference s.symbol θ := by
    rw [circleDifference_congr_ae _ _ s.Hcircle_trace_ae]
    exact hardyQTrace_difference_sharp s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower
      s.M s.M_nonneg s.upper θ
  have hPD (θ : HardyCircle) : circleDifference s.Pcircle θ ≤
      1 / (2 * s.m ^ 3) * circleDifference s.symbol θ := by
    rw [circleDifference_congr_ae _ _ s.Pcircle_trace_ae]
    exact hardyPTrace_difference_sharp s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower
      s.M s.M_nonneg s.upper θ
  constructor
  · have h := halfSobolevSq_of_circleDifference_bound s.Hcircle s.symbol
      (s.Hcircle_continuous hH) s.symbol_continuous _ (by positivity) hHD
    simpa only [Hcircle_coe, symbol, periodicSymbol_coe] using h
  · have h := halfSobolevSq_of_circleDifference_bound s.Pcircle s.symbol
      (s.Pcircle_continuous hP) s.symbol_continuous _ (by positivity) hPD
    simpa only [Pcircle_coe, symbol, periodicSymbol_coe] using h

theorem interior_bounds (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    matOpNormR (s.H z) ≤ Real.sqrt s.M ∧ matOpNormR (s.Hinv z) ≤ (Real.sqrt s.m)⁻¹ := by
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  exact ⟨hardyQ_bound s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper z hn,
    hardyP_bound s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper z hn⟩

end BoundarySource
end Yau.NodeProofs.D06Aux
