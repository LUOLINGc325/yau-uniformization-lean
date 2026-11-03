import Yau.Proofs.P03RadialKernel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped Topology ContDiff
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

def scaledRadialKernel (t : ℝ) (x : ComplexVector n) : ℝ :=
  (t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * radialKernel 1 (t⁻¹ • x)

theorem scaledRadialKernel_contDiff (t : ℝ) :
    ContDiff ℝ ∞ (scaledRadialKernel (n := n) t) :=
  contDiff_const.mul ((radialKernel_contDiff 1).comp (contDiff_id.const_smul t⁻¹))

theorem scaledRadialKernel_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : ComplexVector n, scaledRadialKernel t x) = 1 := by
  change (∫ x : ComplexVector n, (t ^ Module.finrank ℝ (ComplexVector n))⁻¹ *
    radialKernel 1 (t⁻¹ • x)) = 1
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume _ ht.le,
    smul_eq_mul, radialKernel_integral (by norm_num : (0 : ℝ) < 1), mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

theorem scaledRadialKernel_rotation (t : ℝ) (c : ℂ) (hc : ‖c‖ = 1)
    (x : ComplexVector n) : scaledRadialKernel t (c • x) = scaledRadialKernel t x := by
  unfold scaledRadialKernel
  rw [smul_comm t⁻¹ c x, radialKernel_rotation 1 c hc]

theorem scaledRadialKernel_tsupport_subset {t : ℝ} (ht : 0 < t) :
    tsupport (scaledRadialKernel (n := n) t) ⊆ Metric.closedBall 0 t := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hk : radialKernel 1 (t⁻¹ • x) ≠ 0 := by
    intro hz
    exact hx (by simp only [scaledRadialKernel, hz, mul_zero])
  have hnorm : ‖t⁻¹ • x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      radialKernel_tsupport_subset (n := n) (by norm_num : (0 : ℝ) < 1) (subset_closure hk)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] at hnorm
  have hxle : ‖x‖ ≤ t := by
    have h := mul_le_mul_of_nonneg_left hnorm ht.le
    simpa only [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul, mul_one] using h
  simpa only [Metric.mem_closedBall, dist_zero_right] using hxle

theorem scaledRadialKernel_hasCompactSupport {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (scaledRadialKernel (n := n) t) :=
  (isCompact_closedBall (0 : ComplexVector n) t).of_isClosed_subset (isClosed_tsupport _)
    (scaledRadialKernel_tsupport_subset ht)

theorem scaledRadialKernel_iteratedFDeriv (t : ℝ) (j : ℕ) (x : ComplexVector n) :
    iteratedFDeriv ℝ j (scaledRadialKernel (n := n) t) x =
      ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * (t⁻¹) ^ j) •
        iteratedFDeriv ℝ j (radialKernel 1) (t⁻¹ • x) := by
  have hcomp : ContDiff ℝ ∞ (fun x : ComplexVector n => radialKernel 1 (t⁻¹ • x)) :=
    (radialKernel_contDiff 1).comp (contDiff_id.const_smul t⁻¹)
  change iteratedFDeriv ℝ j
    ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ •
      (fun x : ComplexVector n => radialKernel 1 (t⁻¹ • x))) x = _
  rw [iteratedFDeriv_const_smul_apply (hcomp.contDiffAt.of_le (by simp)),
    congrFun (iteratedFDeriv_comp_const_smul t⁻¹
      ((radialKernel_contDiff (n := n) 1).of_le (show (j : ℕ∞ω) ≤ ∞ by simp))) x,
    smul_smul]

theorem exists_scaledRadialKernel_jet_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 < t → ∀ x : ComplexVector n,
      ‖iteratedFDeriv ℝ j (scaledRadialKernel t) x‖ ≤
        (t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * (t⁻¹) ^ j * C := by
  have hc := (radialKernel_hasCompactSupport (n := n) (by norm_num : (0 : ℝ) < 1)).iteratedFDeriv
    (𝕜 := ℝ) j
  have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ j (radialKernel (n := n) 1)) :=
    (radialKernel_contDiff 1).iteratedFDeriv_right (by simp)
  obtain ⟨A, hA⟩ := hD.continuous.bounded_above_of_compact_support hc
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro t ht x
  rw [scaledRadialKernel_iteratedFDeriv, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _))
      (pow_nonneg (inv_nonneg.mpr ht.le) _))]
  exact mul_le_mul_of_nonneg_left ((hA _).trans (le_max_left _ _)) (by positivity)

end Yau.NodeProofs.P03Aux
