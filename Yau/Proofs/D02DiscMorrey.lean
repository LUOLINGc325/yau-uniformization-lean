import Yau.Proofs.D02GradientLp

/-! The original L09 theorem applies to the actual distance functions.
Choosing the target point after the common gradient bound gives a uniform
Hölder estimate for the manifold-valued discs themselves. -/

open scoped Topology ContDiff ENNReal
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem uniform_disc_morrey_of_exp_bound {n N : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (fs : ℕ → ℂ → M.Carrier) (hfs : ∀ j, IsHolomorphicDisc (fs j))
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hdisc : closedBall z₀ (2 * r) ⊆ ball (0 : ℂ) 1)
    (B D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hu : ∀ j z, z ∈ ball z₀ (2 * r) → immersionDifferentialNormSq g.form F (fs j z) ≤ B)
    (hdF : ∀ j z, z ∈ ball z₀ (2 * r) → ‖deriv (fun w => F (fs j w)) z‖ ≤ D)
    (hExp : ∀ j, IntegrableOn
      (fun z => Real.exp (-((3 : ℝ) / 2) * immersionPotential g.form F (fs j z)))
      (ball z₀ (2 * r)) volume ∧
      (∫ z in ball z₀ (2 * r), Real.exp (-((3 : ℝ) / 2) * immersionPotential g.form F (fs j z))) ≤ C) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ j z, z ∈ ball z₀ r → ∀ w, w ∈ ball z₀ r →
      lengthDist g.form (fs j z) (fs j w) ≤ H * ‖z - w‖ ^ (1 / 3 : ℝ) := by
  obtain ⟨C₀, hC₀, hMorrey⟩ := planarMorrey
  let L : ℝ := ((Real.sqrt (4 * max 1 B ^ (n - 1) * D ^ 2)) ^ 3 * C) ^ (1 / 3 : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨C₀ * L, mul_nonneg hC₀.le hL, fun j z hz w hw => ?_⟩
  obtain ⟨G, hcont, hweak, hmem, hnorm⟩ := distanceGradient_memLp_three g hF hImm (hfs j)
    (fs j w) z₀ (2 * r) hdisc B D C hD (hu j) (hdF j) (hExp j).1 (hExp j).2
  have hm := (hMorrey z₀ r hr _ G hcont hweak hmem z hz w hw).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hC₀.le)
      (Real.rpow_nonneg (norm_nonneg _) _))
  letI := L12Aux.inducedMetricSpace g
  change |dist (fs j z) (fs j w) - dist (fs j w) (fs j w)| ≤ _ at hm
  change dist (fs j z) (fs j w) ≤ C₀ * L * ‖z - w‖ ^ (1 / 3 : ℝ)
  simpa only [L, dist_self, sub_zero, abs_of_nonneg dist_nonneg] using hm

end Yau.NodeProofs.D02Aux
