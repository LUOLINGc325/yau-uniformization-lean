import Yau.Proofs.D02PunctureLocalization
import Yau.Proofs.D02AreaScaling

/-! Affine rescaling of the actual physical derivative has cancelling
squared-velocity and planar-area factors. This supplies the unweighted
section-integral input to the original D03. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem setLIntegral_complex_add (a : ℂ) (S : Set ℂ) (hS : MeasurableSet S)
    (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in (fun w => a + w) ⁻¹' S, q (a + z)) = ∫⁻ w in S, q w := by
  have he : MeasurableEmbedding (fun z : ℂ => a + z) :=
    (Homeomorph.addLeft a).toMeasurableEquiv.measurableEmbedding
  rw [← lintegral_indicator (hS.preimage he.measurable), ← lintegral_indicator hS]
  have hi : ((fun w => a + w) ⁻¹' S).indicator (fun z => q (a + z)) =
      fun z => S.indicator q (a + z) := by
    funext z
    by_cases hz : a + z ∈ S <;> simp [Set.indicator, hz]
  rw [hi]
  exact (measurePreserving_add_left (volume : Measure ℂ) a).lintegral_comp_emb he (S.indicator q)

theorem setLIntegral_affine_energy (z₀ : ℂ) (R : ℝ) (hR : 0 < R) (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in puncturedUnitDisc, ENNReal.ofReal (R ^ 2) * q (z₀ + (R : ℂ) * z)) =
      ∫⁻ w in {w : ℂ | 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < R}, q w := by
  have h := weighted_setLIntegral_rescale R hR 1 0 (fun w => q (z₀ + w))
  simp only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one, mul_one, one_mul] at h
  have hS : MeasurableSet {w : ℂ | 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < R} :=
    ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)).measurableSet
  have hpre : (fun w : ℂ => z₀ + w) ⁻¹' {w : ℂ | 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < R} =
      {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R} := by
    ext w
    simp only [mem_preimage, mem_setOf_eq, add_sub_cancel_left]
  rw [← setLIntegral_complex_add z₀ _ hS q, hpre]
  simpa only [puncturedUnitDisc, Complex.real_smul] using h

theorem rescaledCurve_unweighted_energy {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (f : ℂ → M.Carrier) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f
      {w : ℂ | 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < R}) :
    (∫⁻ z in puncturedUnitDisc, ENNReal.ofReal (hermitianNormSq (g (rescaledCurve f z₀ R z))
      (physicalCurveDerivative (rescaledCurve f z₀ R) z))) =
      ∫⁻ w in {w : ℂ | 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < R},
        ENNReal.ofReal (hermitianNormSq (g (f w)) (physicalCurveDerivative f w)) := by
  rw [← setLIntegral_affine_energy z₀ R hR]
  apply setLIntegral_congr_fun
    (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet : MeasurableSet puncturedUnitDisc)
  intro z hz
  have hO : IsOpen {w : ℂ | 0 < ‖w - z₀‖ ∧ ‖w - z₀‖ < R} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hzO := rescaledCurve_parameter_mem z₀ hR (Subset.refl _) hz
  have he := rescaledCurve_energyDensity g f z₀ R z (hf.mdifferentiableAt (hO.mem_nhds hzO))
  dsimp only []
  rw [he, ENNReal.ofReal_mul (sq_nonneg R)]

end Yau.NodeProofs.D02Aux
