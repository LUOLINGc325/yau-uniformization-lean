import Yau.Proofs.D02DistanceGradient
import Yau.Proofs.D02DiscInverse

/-! The inverse immersion estimate controls genuine weak gradients in
L³ by the exponential estimate for the same Jacobian potential. -/

open scoped Topology ContDiff ENNReal
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem sqrt_energy_cube_le {q D t : ℝ} (hD : 0 ≤ D) (hq : q ≤ D * Real.exp (-t)) :
    (Real.sqrt (2 * q)) ^ 3 ≤
      (Real.sqrt (2 * D)) ^ 3 * Real.exp (-((3 : ℝ) / 2) * t) := by
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2))
  have heq : Real.sqrt (2 * (D * Real.exp (-t))) =
      Real.sqrt (2 * D) * Real.exp (-t / 2) := by
    have he : Real.sqrt (Real.exp (-t)) = Real.exp (-t / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1 <;> ring
    rw [← mul_assoc, Real.sqrt_mul (by positivity), he]
  rw [heq] at hs
  calc
    _ ≤ (Real.sqrt (2 * D) * Real.exp (-t / 2)) ^ 3 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 3
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2 <;> ring

theorem memLp_three_of_norm_cube_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {ν : Measure α} {G : α → E} (hG : AEStronglyMeasurable G ν)
    {a : α → ℝ} (ha : Integrable a ν) {D C : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ᵐ z ∂ν, ‖G z‖ ^ 3 ≤ D * a z) (hint : (∫ z, a z ∂ν) ≤ C) :
    MemLp G 3 ν ∧ (eLpNorm G 3 ν).toReal ≤ (D * C) ^ (1 / 3 : ℝ) := by
  have hcube : Integrable (fun z => ‖G z‖ ^ 3) ν := by
    apply (ha.const_mul D).mono' (hG.norm.pow 3)
    exact hbound.mono (fun z hz => by
      change ‖‖G z‖ ^ 3‖ ≤ D * a z
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖G z‖ ^ 3)] using hz)
  have hmem : MemLp G 3 ν := (integrable_norm_rpow_iff (p := 3) hG (by norm_num) (by norm_num)).mp (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using hcube)
  refine ⟨hmem, ?_⟩
  have hi : (∫ z, ‖G z‖ ^ 3 ∂ν) ≤ D * C := by
    calc
      _ ≤ ∫ z, D * a z ∂ν := integral_mono_ae hcube (ha.const_mul D) hbound
      _ = D * ∫ z, a z ∂ν := integral_const_mul _ _
      _ ≤ D * C := mul_le_mul_of_nonneg_left hint hD
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity)]
  have hn0 : 0 ≤ ∫ z, ‖G z‖ ^ 3 ∂ν := integral_nonneg (fun z => by positivity)
  simpa only [one_div] using Real.rpow_le_rpow hn0 hi (by norm_num : (0 : ℝ) ≤ 1 / 3)

theorem distanceGradient_memLp_three {n N : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (p : M.Carrier)
    (z₀ : ℂ) (r : ℝ) (hdisc : closedBall z₀ r ⊆ ball (0 : ℂ) 1)
    (B D C : ℝ) (hD : 0 ≤ D)
    (hu : ∀ z ∈ ball z₀ r, immersionDifferentialNormSq g.form F (f z) ≤ B)
    (hdF : ∀ z ∈ ball z₀ r, ‖deriv (fun w => F (f w)) z‖ ≤ D)
    (hExp : IntegrableOn (fun z => Real.exp (-((3 : ℝ) / 2) * immersionPotential g.form F (f z)))
      (ball z₀ r) volume)
    (hExpC : (∫ z in ball z₀ r,
      Real.exp (-((3 : ℝ) / 2) * immersionPotential g.form F (f z))) ≤ C) :
    ∃ G : ℂ → LeafCandidates.RV 2,
      ContinuousOn (fun z => lengthDist g.form (f z) p) (ball z₀ r) ∧
      LeafCandidates.WeakPlanarGradient (ball z₀ r) (fun z => lengthDist g.form (f z) p) G ∧
      MemLp G 3 (volume.restrict (ball z₀ r)) ∧
      (eLpNorm G 3 (volume.restrict (ball z₀ r))).toReal ≤
        ((Real.sqrt (4 * max 1 B ^ (n - 1) * D ^ 2)) ^ 3 * C) ^ (1 / 3 : ℝ) := by
  obtain ⟨G, hcont, hweak, hG⟩ := distanceFunction_exists_actualWeakGradient g hf p z₀ r hdisc
  let T : ℝ := 2 * max 1 B ^ (n - 1) * D ^ 2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hq : ∀ z ∈ ball z₀ r, closedDiscDensity g.form f z ≤
      T * Real.exp (-immersionPotential g.form F (f z)) := by
    intro z hz
    have hi := discDensity_inverse_bound g.form hF hImm hf B (hdisc (ball_subset_closedBall hz)) (hu z hz)
    have hd : ‖deriv (fun w => F (f w)) z‖ ^ 2 ≤ D ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdF z hz) 2
    calc
      _ ≤ 2 * max 1 B ^ (n - 1) * Real.exp (-immersionPotential g.form F (f z)) *
          ‖deriv (fun w => F (f w)) z‖ ^ 2 := hi
      _ ≤ 2 * max 1 B ^ (n - 1) * Real.exp (-immersionPotential g.form F (f z)) * D ^ 2 :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by dsimp [T]; ring
  have hcube : ∀ᵐ z ∂volume.restrict (ball z₀ r),
      ‖G z‖ ^ 3 ≤ (Real.sqrt (2 * T)) ^ 3 *
        Real.exp (-((3 : ℝ) / 2) * immersionPotential g.form F (f z)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (pow_le_pow_left₀ (norm_nonneg _) (hG z hz) 3).trans (sqrt_energy_cube_le hT (hq z hz))
  obtain ⟨hmem, hnorm⟩ := memLp_three_of_norm_cube_bound hweak.2.1.aestronglyMeasurable hExp
    (by positivity : 0 ≤ (Real.sqrt (2 * T)) ^ 3) hcube hExpC
  refine ⟨G, hcont, hweak, hmem, ?_⟩
  have heq : 2 * T = 4 * max 1 B ^ (n - 1) * D ^ 2 := by dsimp [T]; ring
  simpa only [heq] using hnorm

end Yau.NodeProofs.D02Aux
