import Yau.Proofs.P08RegularizedLog
import Yau.Proofs.P04HolomorphicNormSmooth

/-! Fatou passage from smooth positive regularizations to the frozen actual
real logarithm; the zero set is dealt with independently of `Real.log 0`. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs

/-- The value `Real.log 0 = 0` gives the required Fatou inequality at zeros;
continuity of the logarithm gives equality everywhere else. -/
theorem ofReal_abs_log_le_liminf_regularized (q : ℝ) :
    ENNReal.ofReal |Real.log q| ≤
      liminf (fun j => ENNReal.ofReal |Real.log (q + logRegularizationParameter j)|) atTop := by
  by_cases hq : q = 0
  · simp only [hq, Real.log_zero, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (regularized_log_tendsto hq).abs
    exact ht.liminf_eq.ge

/-- No a priori integrability of the singular logarithm is needed for this
passage. The bound can already be a ball-volume multiple. -/
theorem lintegral_abs_log_le_of_regularizations {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q : α → ℝ) (hq : Measurable q) (B : ℝ≥0∞)
    (hbound : ∀ j : ℕ,
      (∫⁻ x, ENNReal.ofReal |Real.log (q x + logRegularizationParameter j)| ∂μ) ≤ B) :
    (∫⁻ x, ENNReal.ofReal |Real.log (q x)| ∂μ) ≤ B := by
  calc
    _ ≤ ∫⁻ x, liminf (fun j => ENNReal.ofReal
        |Real.log (q x + logRegularizationParameter j)|) atTop ∂μ :=
      lintegral_mono (fun x => ofReal_abs_log_le_liminf_regularized (q x))
    _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal
        |Real.log (q x + logRegularizationParameter j)| ∂μ) atTop :=
      lintegral_liminf_le (fun j => ENNReal.measurable_ofReal.comp
        ((Real.measurable_log.comp (hq.add_const _)).abs))
    _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- A finite uniform bound forces the zero set to be null even though the
frozen real logarithm is assigned the value zero there. -/
theorem zero_set_null_of_regularized_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q : α → ℝ) (hq : Measurable q) (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∀ j : ℕ,
      (∫⁻ x, ENNReal.ofReal |Real.log (q x + logRegularizationParameter j)| ∂μ) ≤ B) :
    μ {x | q x = 0} = 0 := by
  let G : α → ℝ≥0∞ := fun x => liminf (fun j =>
    ENNReal.ofReal |Real.log (q x + logRegularizationParameter j)|) atTop
  have hm (j : ℕ) : Measurable (fun x =>
      ENNReal.ofReal |Real.log (q x + logRegularizationParameter j)|) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_log.comp (hq.add_const _)).abs)
  have hG : Measurable G := Measurable.liminf hm
  have hi : (∫⁻ x, G x ∂μ) < ⊤ :=
    (lintegral_liminf_le hm).trans_lt
      (lt_of_le_of_lt (liminf_le_of_frequently_le' (Frequently.of_forall hbound)) hB)
  have hae := ae_lt_top hG hi.ne
  suffices ∀ᵐ x ∂μ, q x ≠ 0 by
    simpa only [ne_eq, not_not] using (ae_iff.mp this)
  filter_upwards [hae] with x hx
  change ¬ q x = 0
  intro hzero
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal
      |Real.log (q x + logRegularizationParameter j)|) atTop (𝓝 ⊤) := by
    have heq : (fun j : ℕ => ENNReal.ofReal
        |Real.log (q x + logRegularizationParameter j)|) =
        (fun j : ℕ => ENNReal.ofReal ((j : ℝ) + 1)) := by
      funext j
      simp only [hzero, zero_add, log_logRegularizationParameter, abs_neg,
        abs_of_nonneg (show 0 ≤ (j : ℝ) + 1 by positivity)]
    rw [heq]
    exact ENNReal.tendsto_ofReal_atTop.comp
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop))
  exact hx.ne (hlim.liminf_eq)

variable {n : ℕ} {M : ComplexManifold n}

/-- Uniform regularized ball estimates imply precisely the original
absolute canonical-logarithm estimate. -/
theorem canonical_log_ball_of_regularized (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (μ : Measure M.Carrier) (o : M.Carrier) (L B : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      BallIntegralLE g.form μ o (fun x => |Real.log (canonicalNormSq g.form S x + ε)|) L B) :
    BallIntegralLE g.form μ o (fun x => |Real.log (canonicalNormSq g.form S x)|) L B := by
  apply lintegral_abs_log_le_of_regularizations (μ.restrict (distBall g.form o L))
    (canonicalNormSq g.form S)
    (L18Aux.continuous_of_smoothFn (Yau.Proofs.P04Aux.canonicalNormSq_smooth g S hS)).measurable
  intro j
  exact hbound _ (logRegularizationParameter_pos j) (logRegularizationParameter_le_one j)

end Yau.NodeProofs.P08Aux
