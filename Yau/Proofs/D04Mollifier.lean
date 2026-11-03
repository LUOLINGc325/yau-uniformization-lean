import Yau.Proofs.D04Convolution
import Yau.Proofs.D04CircleMean

open MeasureTheory Filter Set
open scoped Topology ContDiff Convolution

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- The local real class retains the finite-value assertions. -/
def CoordinateLocallyL1 (O : Set (ComplexVector n)) (u : ComplexVector n → EReal) : Prop :=
  ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ O →
    (∀ᵐ y ∂volume.restrict K, u y ≠ ⊥ ∧ u y ≠ ⊤) ∧
      IntegrableOn (fun y => (u y).toReal) K volume

theorem radialConvolution_eq_add (t : ℝ) (f : ComplexVector n → ℝ) (x : ComplexVector n) :
    (∫ v, radialKernel t v * f (x + v)) = ∫ y, radialKernel t (x - y) * f y := by
  have h := (measurePreserving_add_left (volume : Measure (ComplexVector n)) x).integral_comp
    (MeasurableEquiv.addLeft x).measurableEmbedding
      (fun y => radialKernel t (x - y) * f y)
  simpa only [sub_add_eq_sub_sub, sub_self, zero_sub, radialKernel_neg] using h

theorem radialConvolution_eq_restrict {t : ℝ} (ht : 0 < t)
    (f : ComplexVector n → ℝ) (x : ComplexVector n) :
    (∫ y, radialKernel t (x - y) * f y) =
      ∫ y in Metric.closedBall x (2 * t), radialKernel t (x - y) * f y := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hzero : radialKernel t (x - y) = 0 := by
    by_contra hne
    have hs := radialKernel_tsupport_subset ht (subset_tsupport _ hne)
    apply hy
    simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, dist_zero_right, sub_zero] using hs
  rw [hzero, zero_mul]

/-- Rotation averaging proves the normalized radial submean against every
continuous majorant, with real-volume mass in the actual dimension. -/
theorem continuous_majorant_radial_submean
    {Ω : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u Ω) {x : ComplexVector n} {t q : ℝ} (ht : 0 < t)
    (hball : Metric.closedBall x (2 * t) ⊆ Ω) (hq : (q : EReal) ≤ u x)
    {F : ComplexVector n → ℝ} (hF : Continuous F)
    (hmajor : ∀ y ∈ Metric.closedBall x (2 * t), u y ≤ (F y : EReal)) :
    q ≤ ∫ y, radialKernel t (x - y) * F y := by
  let K : Set (ComplexVector n) := Metric.closedBall 0 (2 * t)
  let G : ComplexVector n → ℝ := fun v => radialKernel t v * F (x + v)
  have hGc : Continuous G :=
    (contDiff_radialKernel t).continuous.mul (hF.comp (continuous_const.add continuous_id))
  obtain ⟨hi, heq⟩ := integral_circleAverage_closedBall hGc (0 : ComplexVector n) (2 * t)
  have hpoint (v : ComplexVector n) :
      circleAverage (fun θ => G (0 + Complex.exp (θ * Complex.I) • v)) =
        radialKernel t v * circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)) := by
    simp only [G, zero_add, radialKernel_rotate, circleAverage]
    rw [intervalIntegral.integral_const_mul]
    ring
  have hiweighted : IntegrableOn
      (fun v => radialKernel t v * circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)))
      K volume := by
    simpa only [hpoint] using hi
  have hmean (v : ComplexVector n) (hv : v ∈ K) :
      q ≤ circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)) := by
    have hvnorm : ‖v‖ ≤ 2 * t := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hv
    have hdisc (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : x + ζ • v ∈ Metric.closedBall x (2 * t) := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      exact (mul_le_mul_of_nonneg_right hζ (norm_nonneg v)).trans (by simpa using hvnorm)
    apply EReal.coe_le_coe_iff.mp
    apply hq.trans
    exact hu.2.2 x v (fun ζ hζ => hball (hdisc ζ hζ))
      (fun θ => F (x + Complex.exp (θ * Complex.I) • v)) (by fun_prop)
      (fun θ => hmajor _ (hdisc _ (by simp)))
  have hzero (v : ComplexVector n) (hv : v ∉ K) : radialKernel t v = 0 := by
    by_contra hne
    exact hv (radialKernel_tsupport_subset ht (subset_tsupport _ hne))
  have hκ : (∫ v in K, radialKernel t v) = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact integral_radialKernel ht
  calc
    q = ∫ v in K, radialKernel t v * q := by rw [integral_mul_const, hκ, one_mul]
    _ ≤ ∫ v in K, radialKernel t v *
        circleAverage (fun θ => F (x + Complex.exp (θ * Complex.I) • v)) :=
      setIntegral_mono_on
        (((contDiff_radialKernel t).continuous.mul continuous_const).continuousOn.integrableOn_compact
          (isCompact_closedBall 0 (2 * t))) hiweighted measurableSet_closedBall
        (fun v hv => mul_le_mul_of_nonneg_left (hmean v hv) (radialKernel_nonneg ht v))
    _ = ∫ v in K, circleAverage (fun θ => G (0 + Complex.exp (θ * Complex.I) • v)) := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro v _
      exact (hpoint v).symm
    _ = ∫ v in K, G v := heq
    _ = ∫ v, radialKernel t v * F (x + v) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by
        change radialKernel t v * F (x + v) = 0
        rw [hzero v hv, zero_mul])
    _ = _ := radialConvolution_eq_add t F x

/-- The original EReal potential is majorized by its actual radial
convolution. The proof uses finite-a.e. facts before converting to the real
class, and never interprets a bottom value as zero. -/
theorem psh_le_radialConvolution
    {O : Set (ComplexVector n)} {u : ComplexVector n → EReal}
    (hu : IsPshOn u O) (hL1 : CoordinateLocallyL1 O u)
    {t : ℝ} (ht : 0 < t) {x : ComplexVector n}
    (hball : Metric.closedBall x (2 * t) ⊆ O) :
    u x ≤ ((∫ y, radialKernel t (x - y) * (u y).toReal : ℝ) : EReal) := by
  let K : Set (ComplexVector n) := Metric.closedBall x (2 * t)
  have hK : IsCompact K := isCompact_closedBall x (2 * t)
  have hx : x ∈ K := Metric.mem_closedBall_self (by positivity)
  obtain ⟨hfinite, hi⟩ := hL1 K hK hball
  obtain ⟨B, hB⟩ := compact_upper_bound hK (hu.2.1.mono hball)
    (fun y hy => hu.1 y (hball hy))
  let C : ℝ := max B 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ y ∈ K, u y ≤ (C : EReal) := fun y hy =>
    (hB y hy).trans (EReal.coe_le_coe_iff.mpr (le_max_left B 0))
  let F : ℕ → ComplexVector n → ℝ := majorantEnvelope K u
  obtain ⟨A, hA⟩ := (radialKernel_hasCompactSupport (n := n) ht).exists_bound_of_continuous
    (contDiff_radialKernel t).continuous
  let D : ℝ := max A 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hkernel (y : ComplexVector n) : ‖radialKernel t (x - y)‖ ≤ D :=
    (hA (x - y)).trans (le_max_left _ _)
  have hconv : Tendsto (fun j => ∫ y in K, radialKernel t (x - y) * F j y) atTop
      (𝓝 (∫ y in K, radialKernel t (x - y) * (u y).toReal)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => D * (|(u y).toReal| + C))
    · exact Filter.Eventually.of_forall fun j =>
        (((contDiff_radialKernel t).continuous.comp (continuous_const.sub continuous_id)).mul
          (majorantEnvelope_lipschitz ⟨x, hx⟩ hC0 hC j).continuous).aestronglyMeasurable.restrict
    · apply Filter.Eventually.of_forall
      intro j
      filter_upwards [hfinite, ae_restrict_mem hK.measurableSet] with y hy hyK
      have hlo := le_coe_majorantEnvelope hC0 hC j hyK
      rw [← EReal.coe_toReal hy.2 hy.1] at hlo
      have hloR := EReal.coe_le_coe_iff.mp hlo
      have hhi := majorantEnvelope_le ⟨x, hx⟩ hC0 hC j y
      have hFn : ‖F j y‖ ≤ |(u y).toReal| + C := by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [neg_abs_le (u y).toReal],
          by linarith [abs_nonneg (u y).toReal]⟩
      rw [norm_mul]
      exact mul_le_mul (hkernel y) hFn (norm_nonneg _) hD0
    · exact (hi.norm.add (integrableOn_const hK.measure_lt_top.ne)).const_mul D
    · filter_upwards [hfinite, ae_restrict_mem hK.measurableSet] with y hy hyK
      have htend := (EReal.tendsto_toReal hy.2 hy.1).comp
        (tendsto_majorantEnvelope hC0 hC (hu.2.1.mono hball) hyK)
      simpa only [Function.comp_def, EReal.toReal_coe] using tendsto_const_nhds.mul htend
  by_contra hnot
  have hlt : ((∫ y, radialKernel t (x - y) * (u y).toReal : ℝ) : EReal) < u x :=
    lt_of_not_ge hnot
  obtain ⟨q, hq, hqu⟩ := EReal.exists_between_coe_real hlt
  have hqbound : q ≤ ∫ y in K, radialKernel t (x - y) * (u y).toReal := by
    apply ge_of_tendsto hconv
    exact Filter.Eventually.of_forall fun j => by
      have h := continuous_majorant_radial_submean hu ht hball hqu.le
        (majorantEnvelope_lipschitz ⟨x, hx⟩ hC0 hC j).continuous
        (fun y hy => le_coe_majorantEnvelope hC0 hC j hy)
      rw [radialConvolution_eq_restrict ht] at h
      exact h
  rw [← radialConvolution_eq_restrict ht] at hqbound
  exact (not_le_of_gt (EReal.coe_lt_coe_iff.mp hq)) hqbound

end Yau.Proofs.D04Aux
