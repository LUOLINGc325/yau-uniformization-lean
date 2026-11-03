import Yau.Proofs.P07SupportWeakLines
import Yau.LeafProofs.L22Convolution

noncomputable section
open Filter Set Metric MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace Yau.NodeProofs.P07Aux.SupportWeak
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux P06Aux
variable {n : ℕ}

/-- A normalized positive convolution preserves the fixed-direction supermean bound. -/
theorem normalized_convolution_supermean
    {F : ComplexVector n → ℝ} (hF : Continuous F)
    (β : ContDiffBump (0 : ComplexVector n))
    (z v : ComplexVector n) (r b : ℝ)
    (hm : ∀ a ∈ closedBall (0 : ComplexVector n) β.rOut,
      angularLineMean F (z - a) v r ≤ F (z - a) + b * r ^ 2) :
    angularLineMean (β.normed volume ⋆[lsmul ℝ ℝ, volume] F) z v r ≤
      (β.normed volume ⋆[lsmul ℝ ℝ, volume] F) z + b * r ^ 2 := by
  let B : Set (ComplexVector n) := closedBall 0 β.rOut
  let κ : ComplexVector n → ℝ := β.normed volume
  have hκ : Continuous κ := β.continuous_normed
  have hBc : IsCompact B := isCompact_closedBall _ _
  have heq (w : ComplexVector n) :
      (∫ a in B, κ a * F (w - a)) = (κ ⋆[lsmul ℝ ℝ, volume] F) w := by
    rw [convolution_def]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro a ha
    have hnot : a ∉ Function.support κ := by
      rw [β.support_normed_eq]
      exact fun h => ha (ball_subset_closedBall h)
    have hz : κ a = 0 := by simpa only [Function.mem_support, not_not] using hnot
    simp only [hz, zero_mul]
  have hprod : Integrable
      (fun p : ComplexVector n × ℝ => κ p.1 *
        F (z + r • (Complex.exp (p.2 * Complex.I) • v) - p.1))
      ((volume.restrict B).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (fun p : ComplexVector n × ℝ => κ p.1 *
        F (z + r • (Complex.exp (p.2 * Complex.I) • v) - p.1)) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact (hBc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Subset.rfl Ioc_subset_Icc_self)
  have hmeani : Integrable
      (fun a => circleAverage (fun θ => κ a *
        F (z + r • (Complex.exp (θ * Complex.I) • v) - a))) (volume.restrict B) := by
    simpa only [circleAverage, intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      hprod.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  have hFi : Integrable (fun a => κ a * F (z - a)) (volume.restrict B) :=
    (hκ.mul (hF.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact hBc
  have hκi : Integrable κ (volume.restrict B) := hκ.continuousOn.integrableOn_compact hBc
  have hκmass : (∫ a in B, κ a) = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact β.integral_normed
    · intro a ha
      have hnot : a ∉ Function.support κ := by
        rw [β.support_normed_eq]
        exact fun h => ha (ball_subset_closedBall h)
      simpa only [Function.mem_support, not_not] using hnot
  have hbound :
      (∫ a in B, circleAverage (fun θ => κ a *
        F (z + r • (Complex.exp (θ * Complex.I) • v) - a))) ≤
      ∫ a in B, κ a * F (z - a) + κ a * (b * r ^ 2) := by
    apply integral_mono_ae hmeani (hFi.add (hκi.mul_const _))
    filter_upwards [ae_restrict_mem hBc.measurableSet] with a ha
    have h := mul_le_mul_of_nonneg_left (hm a ha) (β.nonneg_normed (μ := volume) a)
    unfold angularLineMean at h
    rw [← circleAverage_smul] at h
    have he : (fun θ : ℝ => κ a * F ((z - a) + r • (Complex.exp (θ * Complex.I) • v))) =
        (fun θ : ℝ => κ a * F (z + r • (Complex.exp (θ * Complex.I) • v) - a)) := by
      funext θ
      congr 2
      abel
    rw [he] at h
    simpa only [mul_add, Pi.add_apply, κ] using h
  rw [integral_circleAverage (volume.restrict B)
      (F := fun a θ => κ a * F (z + r • (Complex.exp (θ * Complex.I) • v) - a)) hprod,
    integral_add hFi (hκi.mul_const _), integral_mul_const, hκmass, one_mul, heq] at hbound
  convert hbound using 1
  unfold angularLineMean
  congr 1
  funext θ
  exact (heq _).symm

/-- Supermean at all sufficiently small signed radii controls the smooth directional Levi. -/
theorem leviDirection_le_of_local_supermean
    {u : ComplexVector n → ℝ} (hu : ContDiff ℝ ∞ u)
    (z v : ComplexVector n) (b : ℝ)
    (hm : ∀ᶠ r : ℝ in 𝓝 0, angularLineMean u z v r ≤ u z + b * r ^ 2) :
    leviDirection (leviC u z) v ≤ b := by
  let q : ℝ → ℝ := fun r => u z + b * r ^ 2 - angularLineMean u z v r
  have hmin : IsLocalMin q 0 := by
    filter_upwards [hm] with r hr
    simpa only [q, angularLineMean_zero, zero_pow two_ne_zero, mul_zero, add_zero,
      sub_self] using sub_nonneg.mpr hr
  have hqc : ContinuousAt q 0 :=
    (continuousAt_const.add (continuousAt_const.mul (continuousAt_id.pow 2))).sub
      (hasDerivAt_angularLineMean hu z v 0).continuousAt
  have hn := second_deriv_nonneg_of_localMin hmin hqc
  have hmd : Differentiable ℝ (angularLineMean u z v) :=
    fun r => (hasDerivAt_angularLineMean hu z v r).differentiableAt
  have heq : deriv q = fun r => 2 * b * r - deriv (angularLineMean u z v) r := by
    funext r
    have hd : HasDerivAt (fun r : ℝ => u z + b * r ^ 2) (2 * b * r) r := by
      convert (((hasDerivAt_id r).pow 2).const_mul b).const_add (u z) using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring
    have hder := (hd.sub (hasDerivAt_angularLineMean hu z v r)).deriv
    rw [← (hasDerivAt_angularLineMean hu z v r).deriv] at hder
    exact hder
  rw [heq] at hn
  have hsecond := hasDerivAt_angularLineMean_derivative hu z v 0
  have hdeq : deriv (angularLineMean u z v) =
      (fun r => circleAverage (fun θ => fderiv ℝ u
        (z + r • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v))) :=
    funext (fun r => (hasDerivAt_angularLineMean hu z v r).deriv)
  have hderivdiff : deriv (fun r => 2 * b * r - deriv (angularLineMean u z v) r) 0 =
      2 * b - deriv (deriv (angularLineMean u z v)) 0 := by
    have hlinear : HasDerivAt (fun r : ℝ => 2 * b * r) (2 * b) 0 :=
      by simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul (2 * b)
    have hdmean : DifferentiableAt ℝ (deriv (angularLineMean u z v)) 0 := by
      rw [hdeq]
      exact hsecond.differentiableAt
    simpa only [Pi.sub_def, hlinear.deriv] using deriv_sub hlinear.differentiableAt hdmean
  rw [hderivdiff, second_deriv_angularLineMean hu z v] at hn
  rw [leviDirection_eq_second (hu.contDiffAt.of_le (by simp)),
    directionSecond_eq_hessian (hu.contDiffAt.of_le (by simp)),
    directionSecond_eq_hessian (hu.contDiffAt.of_le (by simp))]
  linarith

end Yau.NodeProofs.P07Aux.SupportWeak
