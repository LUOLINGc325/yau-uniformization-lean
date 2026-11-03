import Yau.Proofs.C02NormalCompositionHolomorphic
import Yau.Proofs.C02NormalCompositionImmersion
import Yau.Proofs.C02NormalCompositionNormalization
import Yau.Proofs.C02NormalCompositionMetricBounds
import Yau.Proofs.C02NormalizedInverseGeometry
import Yau.Proofs.C02NormalizedInverseControl
import Yau.Proofs.C02OpenInverseDifferential
import Yau.Proofs.C02NormalComplexNormalization

/-! A genuine normalized inverse correcting the normal complex structure
gives the exact original UnitaryChart on one numerical receiving ball. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem unitaryChart_of_normalized_inverse
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    (r : ℝ) (hr : 0 < r) (hrρ : 2 * r < radialGaugeRadius K)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (he0 : (0 : ComplexVector n) ∈ e.source)
    (hf : ContDiff ℝ ∞ (e : ComplexVector n → ComplexVector n))
    (hClose : ∀ y ∈ e.source, ‖fderiv ℝ (e : ComplexVector n → ComplexVector n) y -
      ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4)
    (hReceiving : Metric.closedBall (e 0) (3 / 32 : ℝ) ⊆ e.target)
    (hBack : ContDiffOn ℝ ∞ e.symm e.target)
    (hForward : ∀ y ∈ e.source, ∀ v,
      fderiv ℝ (e : ComplexVector n → ComplexVector n) y
          (normalGaugeComplex g p U hU (r • y) v) =
        Complex.I • fderiv ℝ (e : ComplexVector n → ComplexVector n) y v) :
    UnitaryChart g.form p (normalRealMap g p U ∘ normalizedInverseSource e r)
      (r / 128) (1 / 128) 64 := by
  let G := normalizedInverseSource e r
  let O := Metric.ball (0 : ComplexVector n) (r / 128)
  have hDeriv := openPartialHomeomorph_inverse_derivative_norm_le_two e
    (hf.differentiable (by simp)) hClose
  obtain ⟨hG, hRange⟩ := normalizedInverseSource_control e he0 (hClose 0 he0)
    hReceiving hBack hDeriv r hr
  have hNorm (z : ComplexVector n) (hz : z ∈ O) : ‖G z‖ ≤ radialGaugeRadius K :=
    ((hRange z hz).2.trans (by linarith)).le
  have hB (z : ComplexVector n) (hz : z ∈ O) :
      ‖normalDifferential g p U hU (G z) - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4 :=
    (normalGauge_low_order g p U hU hK hRm (G z) (hNorm z hz)).1.trans (by norm_num)
  have hGeo (z : ComplexVector n) (hz : z ∈ O) :=
    normalizedInverseSource_differential_geometry e he0 (hf.differentiable (by simp))
      hClose r hr.ne' z (hRange z hz).1
  have hJ0 (v : ComplexVector n) : normalGaugeComplex g p U hU 0 v = Complex.I • v := by
    rw [normalGaugeComplex_zero]
    rfl
  have hInter (z : ComplexVector n) (hz : z ∈ O) (v : ComplexVector n) :
      fderiv ℝ G z (Complex.I • v) = normalGaugeComplex g p U hU (G z) (fderiv ℝ G z v) :=
    normalizedInverseSource_intertwines e he0 (hf.differentiable (by simp)) hClose
      r hr.ne' (normalGaugeComplex g p U hU) hJ0 hForward z (hRange z hz).1 v
  have hΦ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (normalRealMap g p U ∘ G) O :=
    normal_composition_contMDiffOn g p U hU hK hRm Metric.isOpen_ball hG hNorm hInter
  have hΦAt (z : ComplexVector n) (hz : z ∈ O) :
      MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) (normalRealMap g p U ∘ G) z :=
    ((hΦ z hz).contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp)
  have hz0 : (0 : ComplexVector n) ∈ O := by
    simpa only [O, Metric.mem_ball, dist_self] using (div_pos hr (by norm_num : (0 : ℝ) < 128))
  have hG0 : G 0 = 0 := normalizedInverseSource_zero e he0 r
  have hDG0 := normalizedInverseSource_hasFDerivAt_zero e he0
    (hf.differentiable (by simp) 0) (isInvertible_of_close_identity _ (hClose 0 he0)) r hr.ne'
  refine ⟨⟨hΦ, fun z hz => normal_composition_complex_differential_bijective
    g p U hU (hGeo z hz).1 (hGeo z hz).2.1 (hΦAt z hz) (hB z hz)⟩, ?_, ?_, ?_⟩
  · change normalRealMap g p U (G 0) = p
    rw [hG0, normalRealMap_zero]
  · exact normal_composition_pullback_zero g p U hU hG0 hDG0 (hΦAt 0 hz0)
  · intro z hz
    exact normal_composition_pullback_bounds g p U hU (hGeo z hz).1 (hΦAt z hz)
      (hB z hz) (fun v => ((hGeo z hz).2.2 v).1) (fun v => ((hGeo z hz).2.2 v).2)

end Yau.Blueprint.C02Proof
