import Yau.Proofs.D04Kernel

open MeasureTheory Filter
open scoped Topology ContDiff Convolution

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau

variable {n : ℕ}

/-! The convolution and weighted-defect arguments of L08 are valid in every
finite-dimensional complex Euclidean space. The normalized radial kernels
are constructed by D04Kernel with real-volume mass in that same dimension. -/

/-- The normalized kernels approximate every Lipschitz test function with
a first-order bound, uniform in the evaluation point. -/
theorem radialConvolution_lipschitz_approx {t : ℝ} (ht : 0 < t)
    {χ : (ComplexVector n) → ℝ} {C : NNReal} (hχ : LipschitzWith C χ) (z : (ComplexVector n)) :
    |(∫ w, radialKernel (n := n) t w * χ (z - w)) - χ z| ≤ (C : ℝ) * (2 * t) := by
  have h := MeasureTheory.dist_convolution_le (μ := (volume : Measure (ComplexVector n)))
    (g := χ) (x₀ := z) (R := 2 * t) (z₀ := χ z)
    (mul_nonneg C.coe_nonneg (by positivity : 0 ≤ 2 * t))
    (radialKernel_support_subset_ball ht) (radialKernel_nonneg ht)
    (integral_radialKernel (n := n) ht) hχ.continuous.aestronglyMeasurable
    (fun w hw ↦ (hχ.dist_le_mul w z).trans
      (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hw).le C.coe_nonneg))
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.dist_eq] using h

theorem contDiff_radialConvolution {t : ℝ} (ht : 0 < t) {g : (ComplexVector n) → ℝ}
    (hg : Integrable g volume) :
    ContDiff ℝ ∞ (fun z : (ComplexVector n) ↦ ∫ w, radialKernel (n := n) t (z - w) * g w) := by
  have h := (radialKernel_hasCompactSupport (n := n) ht).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hg.locallyIntegrable (contDiff_radialKernel (n := n) t)
  convert h using 1
  funext z
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards with w
  exact mul_comm _ _

/-- Fubini and symmetry move the smoothing kernel from an integrable
function onto a compactly supported continuous test function. -/
theorem radialConvolution_adjoint {t : ℝ} (ht : 0 < t)
    {g χ : (ComplexVector n) → ℝ} (hg : Integrable g volume) (hχ : Continuous χ)
    (hsχ : HasCompactSupport χ) :
    (∫ z, χ z * (∫ w, radialKernel (n := n) t (z - w) * g w)) =
      ∫ w, g w * (∫ z, radialKernel (n := n) t (w - z) * χ z) := by
  obtain ⟨B, hB⟩ := hsχ.exists_bound_of_continuous hχ
  have hρ : Integrable (radialKernel (n := n) t) volume :=
    integrable_of_integral_eq_one (integral_radialKernel (n := n) ht)
  have hbase := hg.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρ
  change Integrable (fun p : (ComplexVector n) × (ComplexVector n) ↦ g p.2 * radialKernel (n := n) t (p.1 - p.2))
    (volume.prod volume) at hbase
  have hprod : Integrable
      (fun p : (ComplexVector n) × (ComplexVector n) ↦ χ p.1 * (g p.2 * radialKernel (n := n) t (p.1 - p.2)))
      (volume.prod volume) := hbase.bdd_mul
    (hχ.comp continuous_fst).aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ hB p.1)
  calc
    _ = ∫ z, ∫ w, χ z * (g w * radialKernel (n := n) t (z - w)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with w
      exact mul_comm _ _
    _ = ∫ w, ∫ z, χ z * (g w * radialKernel (n := n) t (z - w)) :=
      integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      have hsym : radialKernel (n := n) t (z - w) = radialKernel (n := n) t (w - z) := by
        simpa only [neg_sub] using radialKernel_neg t (w - z)
      rw [hsym]
      ring

theorem integrable_radialConvolution {t : ℝ} (ht : 0 < t) {g : (ComplexVector n) → ℝ}
    (hg : Integrable g volume) :
    Integrable (fun z : (ComplexVector n) ↦ ∫ w, radialKernel (n := n) t (z - w) * g w) volume := by
  have h := hg.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_of_integral_eq_one (integral_radialKernel (n := n) ht))
  convert h using 1
  funext z
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards with w
  exact mul_comm _ _

theorem radialConvolution_lipschitz_approx' {t : ℝ} (ht : 0 < t)
    {χ : (ComplexVector n) → ℝ} {C : NNReal} (hχ : LipschitzWith C χ) (z : (ComplexVector n)) :
    |(∫ w, radialKernel (n := n) t (z - w) * χ w) - χ z| ≤ (C : ℝ) * (2 * t) := by
  have h := radialConvolution_lipschitz_approx ht hχ z
  have heq := convolution_eq_swap (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := (volume : Measure (ComplexVector n))) (f := radialKernel (n := n) t) (g := χ) (x := z)
  change (∫ w, radialKernel (n := n) t w * χ (z - w)) =
    ∫ w, radialKernel (n := n) t (z - w) * χ w at heq
  rwa [heq] at h

/-- The weighted smoothing defect is uniformly small for an L¹-bounded
family. Only a Lipschitz bound on the test function is required. -/
theorem radialConvolution_weighted_defect_bound {t : ℝ} (ht : 0 < t)
    {g χ : (ComplexVector n) → ℝ} (hg : Integrable g volume) {C : NNReal}
    (hχ : LipschitzWith C χ) (hsχ : HasCompactSupport χ) :
    |∫ z, χ z * ((∫ w, radialKernel (n := n) t (z - w) * g w) - g z)| ≤
      ((C : ℝ) * (2 * t)) * ∫ w, |g w| := by
  let p : (ComplexVector n) → ℝ := fun z ↦ ∫ w, radialKernel (n := n) t (z - w) * g w
  let ψ : (ComplexVector n) → ℝ := fun z ↦ ∫ w, radialKernel (n := n) t (z - w) * χ w
  let D := (C : ℝ) * (2 * t)
  obtain ⟨B, hB⟩ := hsχ.exists_bound_of_continuous hχ.continuous
  have hχi : Integrable χ volume := hχ.continuous.integrable_of_hasCompactSupport hsχ
  have hψ : Continuous ψ := (contDiff_radialConvolution ht hχi).continuous
  have hD (w : (ComplexVector n)) : ‖ψ w - χ w‖ ≤ D := radialConvolution_lipschitz_approx' ht hχ w
  have he : Integrable (fun w ↦ g w * (ψ w - χ w)) volume :=
    hg.mul_bdd (hψ.sub hχ.continuous).aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hgχ : Integrable (fun w ↦ g w * χ w) volume :=
    hg.mul_bdd hχ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hgψ : Integrable (fun w ↦ g w * ψ w) volume := by
    apply (he.add hgχ).congr
    filter_upwards with w
    change g w * (ψ w - χ w) + g w * χ w = g w * ψ w
    ring
  have hχp : Integrable (fun w ↦ χ w * p w) volume :=
    (integrable_radialConvolution ht hg).bdd_mul hχ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
  have hχg : Integrable (fun w ↦ χ w * g w) volume := by
    simpa only [mul_comm] using hgχ
  have heq : (∫ z, χ z * (p z - g z)) = ∫ w, g w * (ψ w - χ w) := by
    calc
      _ = (∫ z, χ z * p z) - ∫ z, χ z * g z := by
        simp_rw [mul_sub]
        exact integral_sub hχp hχg
      _ = (∫ w, g w * ψ w) - ∫ w, g w * χ w := by
        rw [radialConvolution_adjoint ht hg hχ.continuous hsχ]
        congr 1
        apply integral_congr_ae
        filter_upwards with w
        exact mul_comm _ _
      _ = _ := by
        rw [← integral_sub hgψ hgχ]
        apply integral_congr_ae
        filter_upwards with w
        ring
  change |∫ z, χ z * (p z - g z)| ≤ D * ∫ w, |g w|
  rw [heq]
  have hn := norm_integral_le_of_norm_le (hg.norm.mul_const D)
    (Filter.Eventually.of_forall fun w ↦
      (norm_mul (g w) (ψ w - χ w)).le.trans
        (mul_le_mul_of_nonneg_left (hD w) (norm_nonneg (g w))))
  rw [Real.norm_eq_abs, integral_mul_const] at hn
  exact hn.trans_eq (mul_comm _ _)

/-- Positivity on the support of a test function turns the weighted defect
estimate into a local L¹ estimate. The comparison is only needed a.e. -/
theorem radialConvolution_L1_error_on {t : ℝ} (ht : 0 < t)
    {g χ : (ComplexVector n) → ℝ} (hg : Integrable g volume) {C : NNReal}
    (hχ : LipschitzWith C χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ z, 0 ≤ χ z) {K : Set (ComplexVector n)} (hK : MeasurableSet K)
    (hχ1 : ∀ z ∈ K, 1 ≤ χ z)
    (hmajor : ∀ᵐ z ∂volume, z ∈ Function.support χ →
      g z ≤ ∫ w, radialKernel (n := n) t (z - w) * g w) :
    (∫ z in K, |(∫ w, radialKernel (n := n) t (z - w) * g w) - g z|) ≤
      ((C : ℝ) * (2 * t)) * ∫ w, |g w| := by
  let p : (ComplexVector n) → ℝ := fun z ↦ ∫ w, radialKernel (n := n) t (z - w) * g w
  have hp : Integrable p volume := integrable_radialConvolution ht hg
  have hi : Integrable (fun z ↦ |p z - g z|) volume := (hp.sub hg).norm
  obtain ⟨B, hB⟩ := hsχ.exists_bound_of_continuous hχ.continuous
  have hw : Integrable (fun z ↦ χ z * (p z - g z)) volume :=
    (hp.sub hg).bdd_mul hχ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hn : ∀ᵐ z ∂volume, 0 ≤ χ z * (p z - g z) := by
    filter_upwards [hmajor] with z hz
    by_cases hzero : χ z = 0
    · simp only [hzero, zero_mul, le_refl]
    · exact mul_nonneg (hχ0 z) (sub_nonneg.mpr (hz hzero))
  have hpoint : ∀ᵐ z ∂volume.restrict K, |p z - g z| ≤ χ z * (p z - g z) := by
    filter_upwards [ae_restrict_of_ae hmajor, ae_restrict_mem hK] with z hz hzK
    have hpos : χ z ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (hχ1 z hzK))
    have hd : 0 ≤ p z - g z := sub_nonneg.mpr (hz hpos)
    rw [abs_of_nonneg hd]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ1 z hzK) hd
  calc
    _ ≤ ∫ z in K, χ z * (p z - g z) :=
      integral_mono_ae (hi.mono_measure Measure.restrict_le_self)
        (hw.mono_measure Measure.restrict_le_self) hpoint
    _ ≤ ∫ z, χ z * (p z - g z) := setIntegral_le_integral hw hn
    _ ≤ |∫ z, χ z * (p z - g z)| := le_abs_self _
    _ ≤ _ := radialConvolution_weighted_defect_bound ht hg hχ hsχ

/-- A compact truncation leaves the convolution unchanged whenever the
whole kernel neighborhood lies in that truncation. -/
theorem radialConvolution_indicator_eq {t : ℝ} (ht : 0 < t)
    (f : (ComplexVector n) → ℝ) {S : Set (ComplexVector n)} {z : (ComplexVector n)} (hball : Metric.closedBall z (2 * t) ⊆ S) :
    (∫ w, radialKernel (n := n) t (z - w) * S.indicator f w) =
      ∫ w, radialKernel (n := n) t (z - w) * f w := by
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw]
  · have hk : radialKernel (n := n) t (z - w) = 0 := by
      by_contra hne
      have hs := radialKernel_tsupport_subset (n := n) ht (subset_tsupport _ hne)
      have hnorm : ‖z - w‖ ≤ 2 * t := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hs
      apply hw
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa only [norm_sub_rev] using hnorm
    rw [hk, zero_mul, zero_mul]

end Yau.Proofs.D04Aux
