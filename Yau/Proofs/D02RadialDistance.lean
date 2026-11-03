import Yau.Proofs.D02RadialVelocity
import Yau.Proofs.D02GoodAngles

/-! The genuine length distance along a radial curve is controlled by
the same radial area energy. The harmless enlarged radius `2B+1` follows
from `sqrt q ≤ q+1` and avoids assumptions on derivatives at the circle. -/

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem radialCurve_edist_le_energy (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (θ : ℝ) {r : ℝ}
    (hr : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) :
    lengthEDist g.form (radialCurve f θ r) (radialCurve f θ 1) ≤
      2 * radialEnergy (discEnergyDensity g.form f) θ + 1 := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => L12Aux.underlyingRealTangentNormedAddCommGroup g.form y
  let γ := radialCurve f θ
  let Q := discEnergyDensity g.form f
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hc : ContinuousOn γ (Icc r 1) := (radialCurve_continuousOn hf θ).mono
    (fun _ ht => ⟨hr0.le.trans ht.1, ht.2⟩)
  have hd : ∀ t ∈ Ioo r 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ t :=
    fun t ht => radialCurve_contMDiffAt_real hf θ ⟨hr0.trans ht.1, ht.2⟩
  have hdist : lengthEDist g.form (γ r) (γ 1) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ r 1 := by
    rw [lengthEDist, L12Aux.inducedDistance_eq_riemannianEDist g]
    exact L12Aux.riemannianEDist_le_pathELength_of_contMDiffAt_Ioo g hr1.le hc hd
  have hpath : Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ r 1 =
      ∫⁻ t in Ioo r 1, ENNReal.ofReal (Real.sqrt (closedDiscDensity g.form f (polarRay t θ))) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change ‖L12Aux.realCurveVelocity (radialCurve f θ) t‖ₑ = _
    rw [← ofReal_norm]
    exact congrArg ENNReal.ofReal (radialCurve_speed g.form hf θ ⟨hr0.trans ht.1, ht.2⟩)
  have hpoint : ∀ t ∈ Ioo r 1,
      ENNReal.ofReal (Real.sqrt (closedDiscDensity g.form f (polarRay t θ))) ≤
        2 * (ENNReal.ofReal t * Q (polarRay t θ)) + 1 := by
    intro t ht
    have ht0 : 0 < t := hr0.trans ht.1
    have hhalf : (1 / 2 : ℝ) ≤ t := hr.trans ht.1.le
    have hz : polarRay t θ ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, polarRay_norm, abs_of_pos ht0] using ht.2
    let q := closedDiscDensity g.form f (polarRay t θ)
    have hq : 0 ≤ q := closedDiscDensity_nonneg _ _ _
    have hs : Real.sqrt q ≤ 2 * t * q + 1 := by
      have hsq := Real.sq_sqrt hq
      have haux := sq_nonneg (Real.sqrt q - 1)
      have hmul : 0 ≤ (2 * t - 1) * q := mul_nonneg (by linarith) hq
      nlinarith [Real.sqrt_nonneg q]
    have hQ : Q (polarRay t θ) = ENNReal.ofReal q := Set.indicator_of_mem hz _
    have he : (2 : ℝ≥0∞) * (ENNReal.ofReal t * ENNReal.ofReal q) + 1 =
        ENNReal.ofReal (2 * (t * q) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul ht0.le]
      norm_num
    rw [hQ, he]
    exact ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hs)
  have hint : (∫⁻ t in Ioo r 1,
      ENNReal.ofReal (Real.sqrt (closedDiscDensity g.form f (polarRay t θ)))) ≤
      2 * radialEnergy Q θ + 1 := by
    calc
      _ ≤ ∫⁻ t in Ioo r 1, 2 * (ENNReal.ofReal t * Q (polarRay t θ)) + 1 :=
        setLIntegral_mono' measurableSet_Ioo hpoint
      _ = 2 * (∫⁻ t in Ioo r 1, ENNReal.ofReal t * Q (polarRay t θ)) +
          volume (Ioo r 1) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' 2 _ (by norm_num)]
        simp
      _ ≤ 2 * radialEnergy Q θ + 1 := by
        apply add_le_add
        · gcongr
          exact lintegral_mono_set (fun t ht => ⟨hr.trans_lt ht.1, ht.2⟩)
        · rw [Real.volume_Ioo]
          exact (ENNReal.ofReal_le_ofReal (by linarith : 1 - r ≤ (1 : ℝ))).trans_eq ENNReal.ofReal_one
  exact hdist.trans (hpath ▸ hint)

theorem goodAngle_radialDistance (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (A : ℝ)
    {θ : ℝ} (hθ : θ ∈ goodAngles (discEnergyDensity g.form f) A)
    {r : ℝ} (hr : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) :
    lengthDist g.form (f (polarRay r θ)) (f (polarRay 1 θ)) ≤
      2 * radialEnergyThreshold A + 1 := by
  have hB := (radialEnergyThreshold_pos A).le
  have hbound : 2 * radialEnergy (discEnergyDensity g.form f) θ + 1 ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal (radialEnergyThreshold A) + 1 := by
    gcongr
    exact hθ.2.le
  have hb := (radialCurve_edist_le_energy g hf θ hr hr1).trans hbound
  have he : (2 : ℝ≥0∞) * ENNReal.ofReal (radialEnergyThreshold A) + 1 =
      ENNReal.ofReal (2 * radialEnergyThreshold A + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

end Yau.NodeProofs.D02Aux
