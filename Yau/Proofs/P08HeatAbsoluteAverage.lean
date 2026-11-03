import Yau.Proofs.P08HeatSubmean
import Yau.Proofs.P08HeatMeasureBallLower

/-! Uniform absolute heat averages use only a uniform upper growth constant
and a basepoint lower bound. The auxiliary global lower bound cancels. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs L12Aux L18Aux L19Aux HeatMeasure
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem linear_subharmonic_abs_heat_average (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {w : M.Carrier → ℝ} (hw : SmoothFn w) (hΔ : ∀ x, 0 ≤ laplacian g.form w x)
    {b A w₀ L : ℝ} (hb : ∀ x, b ≤ w x) (hA : 0 ≤ A)
    (hgrowth : ∀ x, w x ≤ A * (1 + distFrom g.form o x)) (hbase : w₀ ≤ w o) (hL : 1 ≤ L) :
    Integrable (fun x => |w x|)
      (heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)) ∧
    (∫ x, |w x| ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)) ≤
      (2 * A * (2 * n + 2) + |w₀| + 1) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
  letI : IsFiniteMeasure ν := heatEvalMeasure_isFinite hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
  have hmass : ν Set.univ = 1 := heatEvalMeasure_mass hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
  have hwabs (x : M.Carrier) : |w x| ≤ (A + |b|) + A * distFrom g.form o x := by
    have hr : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
    have hAr := mul_nonneg hA hr
    exact abs_le.mpr ⟨by nlinarith [hb x, neg_abs_le b], by nlinarith [hgrowth x, abs_nonneg b]⟩
  have hwi : Integrable w ν := heatEvalMeasure_integrable_linear hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
    (continuous_of_smoothFn hw).aestronglyMeasurable hwabs
  have hri : Integrable (distFrom g.form o) ν :=
    heatEvalMeasure_integrable_distance hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
  have hmajor := integral_mono_ae hwi.abs
    (((integrable_const (1 : ℝ)).add hri).const_mul (2 * A) |>.sub hwi) (ae_of_all ν (fun x => by
      change |w x| ≤ 2 * A * (1 + distFrom g.form o x) - w x
      have hr : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
      have hu := hgrowth x
      rcases le_total 0 (w x) with hx | hx
      · rw [abs_of_nonneg hx]; linarith
      · rw [abs_of_nonpos hx]
        nlinarith [mul_nonneg hA (show 0 ≤ 1 + distFrom g.form o x by linarith)]))
  have hconst : (∫ _x, (1 : ℝ) ∂ν) = 1 := by
    simp only [integral_const, Measure.real, hmass, ENNReal.toReal_one, one_smul]
  change (∫ x, |w x| ∂ν) ≤ ∫ x, 2 * A * (1 + distFrom g.form o x) - w x ∂ν at hmajor
  have hI : (∫ x, 2 * A * (1 + distFrom g.form o x) - w x ∂ν) =
      2 * A * (1 + ∫ x, distFrom g.form o x ∂ν) - ∫ x, w x ∂ν := by
    calc
      _ = (∫ x, 2 * A * (1 + distFrom g.form o x) ∂ν) - ∫ x, w x ∂ν :=
        integral_sub (((integrable_const (1 : ℝ)).add hri).const_mul (2 * A)) hwi
      _ = 2 * A * (∫ x, 1 + distFrom g.form o x ∂ν) - ∫ x, w x ∂ν := by
        rw [integral_const_mul]
      _ = _ := by rw [integral_add (integrable_const (1 : ℝ)) hri, hconst]
  rw [hI] at hmajor
  have hsub := smooth_subharmonic_linear_heat_submean hn g hcomplete hK hRic μ hμ o hw hΔ hb hA hgrowth
    (by positivity : 0 < 2 * L ^ 2)
  have hmoment := heatEvalMeasure_firstMoment hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
  have hsqrt : Real.sqrt (((2 * n : ℕ) : ℝ) * (2 * L ^ 2)) ≤ (2 * n + 1) * L := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    push_cast
    nlinarith [sq_nonneg (2 * (n : ℝ) * L), sq_nonneg L]
  have hdist : (∫ x, distFrom g.form o x ∂ν) ≤ (2 * n + 1) * L := hmoment.trans hsqrt
  have hmul := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 2 * A by positivity)
  have habsL := mul_nonneg (abs_nonneg w₀) (sub_nonneg.mpr hL)
  have hAL := mul_nonneg hA (sub_nonneg.mpr hL)
  refine ⟨hwi.abs, ?_⟩
  change (∫ x, |w x| ∂ν) ≤ _
  nlinarith [neg_abs_le w₀]

end Yau.NodeProofs.P08Aux
