import Yau.Proofs.C02CorrectedNormalChart
import Yau.Proofs.C02QuantitativeInverseJets
import Yau.Proofs.C02NormalizedInverseJets
import Yau.Proofs.C02NormalCompositionCoefficientJets

/-! A single derivative profile is fixed before the metric, centre,
unitary frame and correcting map. Every derivative uses the same chart. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem exists_uniform_corrected_normal_charts
    (r : ℝ) (hr : 0 < r) (a b : ℕ → ℝ) :
    ∃ d : ℕ → ℝ, ∀ (M : ComplexManifold n) (g : SmoothMetric M) (p : M.Carrier)
      (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
      (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
      (K : ℝ), 0 ≤ K → 2 * r < radialGaugeRadius K →
      (∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K) →
      (∀ i x, ‖x‖ ≤ radialGaugeRadius K →
        ‖iteratedFDeriv ℝ i (normalGaugeMetric g p U hU) x‖ ≤ a i) →
      ∀ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ),
        ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4) →
      (∀ i, 1 ≤ i → ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ),
        ‖iteratedFDeriv ℝ i F x‖ ≤ b i) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ), ∀ v,
        fderiv ℝ F x (normalGaugeComplex g p U hU (r • x) v) = Complex.I • fderiv ℝ F x v) →
      ∃ Φ, UnitaryChart g.form p Φ (r / 128) (1 / 128) 64 ∧
        ∀ m r', 0 < r' → r' < r / 128 → PullbackDerivBound g.form Φ r' m (d m) := by
  obtain ⟨B, hB, hInverse⟩ := exists_uniform_fixed_ball_inverse_jet_bounds
    (E := ComplexVector n) (1 / 4 : ℝ) (by norm_num) b
  let c := normalizedInverseJetMajorant r B
  let d := fun m => finiteJetEnvelope (normalCompositionJetMajorant a c) m
  refine ⟨d, ?_⟩
  intro M g p U hU K hK hrρ hRm hMetric F hF hClose hFJets hForward
  obtain ⟨e, he, hSource, hTarget, hBack, hBackJets⟩ := hInverse F hF hClose hFJets
  have he0 : (0 : ComplexVector n) ∈ e.source := by rw [hSource]; simp
  have heSmooth : ContDiff ℝ ∞ (e : ComplexVector n → ComplexVector n) := by rw [he]; exact hF
  have heClose (x : ComplexVector n) (hx : x ∈ e.source) :
      ‖fderiv ℝ (e : ComplexVector n → ComplexVector n) x -
        ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4 := by
    rw [he]
    exact hClose x (by rwa [← hSource])
  have heForward (x : ComplexVector n) (hx : x ∈ e.source) (v : ComplexVector n) :
      fderiv ℝ (e : ComplexVector n → ComplexVector n) x
        (normalGaugeComplex g p U hU (r • x) v) =
          Complex.I • fderiv ℝ (e : ComplexVector n → ComplexVector n) x v := by
    rw [he]
    exact hForward x (by rwa [← hSource]) v
  have hReceiving : Metric.closedBall (e 0) (3 / 32 : ℝ) ⊆ e.target := by
    rw [he]
    convert hTarget using 1 <;> norm_num
  let G := normalizedInverseSource e r
  let Φ := normalRealMap g p U ∘ G
  have hChart : UnitaryChart g.form p Φ (r / 128) (1 / 128) 64 :=
    unitaryChart_of_normalized_inverse g p U hU hK hRm r hr hrρ e he0 heSmooth heClose
      hReceiving hBack heForward
  have hDeriv := openPartialHomeomorph_inverse_derivative_norm_le_two e
    (heSmooth.differentiable (by simp)) heClose
  obtain ⟨hG, hRange⟩ := normalizedInverseSource_control e he0 (heClose 0 he0)
    hReceiving hBack hDeriv r hr
  have hc (i : ℕ) : 0 ≤ c i := by
    have hEnv := finiteJetEnvelope_one_le B i
    have hLin := finiteJetEnvelope_one_le (fun _ => 3 / r) i
    dsimp only [c, normalizedInverseJetMajorant]
    positivity
  have hGJets (i : ℕ) (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (r / 128)) :
      ‖iteratedFDeriv ℝ i G x‖ ≤ c i :=
    normalizedInverseSource_jet_le e (heClose 0 he0) hBack B hBackJets r hr Metric.isOpen_ball
      (fun z hz => (hRange z hz).1) i hx
  have hΦAt (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (r / 128)) :
      MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ x :=
    (((hChart.1.1 x hx).contMDiffAt (Metric.isOpen_ball.mem_nhds hx))).mdifferentiableAt (by simp)
  refine ⟨Φ, hChart, ?_⟩
  intro m r' hr' hr'r j hj x hx k l
  have hxBig : x ∈ Metric.ball (0 : ComplexVector n) (r / 128) :=
    Metric.ball_subset_ball hr'r.le hx
  have hMetricAt (i : ℕ) :
      ‖iteratedFDeriv ℝ i (normalGaugeMetric g p U hU) (G x)‖ ≤ a i := by
    apply hMetric
    exact ((hRange x hxBig).2.trans (by linarith)).le
  exact (normal_composition_coefficient_jet_bound g p U hU Metric.isOpen_ball hG hΦAt hxBig a c hc
    hMetricAt (fun i hi => hGJets i x hxBig) j k l).trans (le_finiteJetEnvelope _ hj)

end Yau.Blueprint.C02Proof
