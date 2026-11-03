import Yau.Proofs.V02CoronaDensityBound
import Yau.Proofs.V02DiscTraceFull
import Yau.Proofs.V03EnergyTraceBounds

/-! The actual corona correction has a uniform boundary L² and half-order
bound on every original disc in a fixed compact set with bounded energy. -/

open scoped Topology ContDiff Manifold Matrix
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint Yau.LeafProofs

theorem closedDiscDerivative_sq_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : ℂ → E} (hX : ContDiffOn ℂ ∞ X (Metric.closedBall (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, ‖V03Proof.closedDiscDerivative X z‖ ^ 2) =
      (V03Proof.normDiscArea X).toReal / 2 := by
  have he := V03Proof.normDiscArea_radial_eq_integral hX (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul] at he
  have hn : 0 ≤ ∫ z in Metric.ball (0 : ℂ) 1,
      V03Proof.radialEuclideanDensity X 1 z :=
    integral_nonneg (fun z => by dsimp [V03Proof.radialEuclideanDensity]; positivity)
  have ht := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal hn] at ht
  simp only [V03Proof.radialEuclideanDensity, Complex.ofReal_one, one_mul, one_smul,
    integral_const_mul] at ht
  linarith

theorem disc_density_integral_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : ℂ → E} (hX : ContDiffOn ℂ ∞ X (Metric.closedBall (0 : ℂ) 1))
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      ‖u z‖ ^ 2 ≤ A * (1 + ‖fderiv ℂ X z 1‖ ^ 2)) :
    (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖ ^ 2) ≤
      A * (volume.real (Metric.ball (0 : ℂ) 1) + (V03Proof.normDiscArea X).toReal / 2) := by
  have hi : IntegrableOn
      (fun z => ‖V03Proof.closedDiscDerivative X z‖ ^ 2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn ((V03Proof.continuousOn_closedDiscDerivative hX).norm.pow 2)
  have hc : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn continuousOn_const
  have hui : IntegrableOn (fun z => ‖u z‖ ^ 2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (hu.continuousOn.norm.pow 2)
  have hboundi : IntegrableOn
      (fun z => A * (1 + ‖V03Proof.closedDiscDerivative X z‖ ^ 2))
      (Metric.ball (0 : ℂ) 1) := (hc.add hi).const_mul A
  have hh := integral_mono_ae hui hboundi (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      have hD : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
        mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
      simpa only [V03Proof.closedDiscDerivative, fderivWithin_of_mem_nhds hD] using hbound z hz)
  rw [integral_const_mul, integral_add hc hi, closedDiscDerivative_sq_integral hX] at hh
  simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using hh

variable {n q : ℕ} {X : KahlerManifold n}

theorem spanningCoronaCorrection_uniform_trace
    {d : VariationData X q} (hd : VariationSetup d) {b : ℕ}
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (E₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : ℕ) (F : VariationDisc X),
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F.f z ∈ K) →
      ∀ i k : SpanningMinorIndex n q b,
        ENNReal.ofReal (circleAverage (fun θ =>
          ‖coronaDbarCorrection (fun l w => spanningSigma d.G Z l (F.f w)) i k
            (circlePoint θ)‖ ^ 2)) +
          boundaryDSq (fun θ (_ : Unit) =>
            coronaDbarCorrection (fun l w => spanningSigma d.G Z l (F.f w)) i k
              (circlePoint θ)) ≤ ENNReal.ofReal B := by
  obtain ⟨A, hA, hbound⟩ := spanningCoronaDensity_compact_bound hd.2.2.2.2.1 hZ hspan hK
  obtain ⟨C, hC, htrace⟩ := canonicalDbar_boundaryTraceEstimate
  let B := C * A * (volume.real (Metric.ball (0 : ℂ) 1) + max E₀ 0 / 2)
  refine ⟨B, by dsimp [B]; positivity, fun j F hF hE hfK i k => ?_⟩
  have hσ := fun l => spanningSigma_disc_contDiffOn hd.2.2.2.2.1 hZ hspan hF.1 l
  have hu := coronaDbarDensity_contDiffOn hσ i k
  have hi := disc_density_integral_bound
    (V03Proof.cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1) hu hA
    (hbound F.f hF.1 hfK i k)
  have harea : (V03Proof.normDiscArea (fun w => d.G (F.f w))).toReal ≤ max E₀ 0 := by
    exact ((ENNReal.toReal_mono hF.2.2.2.2.2.2.2.2
      (V03Proof.euclideanArea_le_variationEnergy d j F)).trans hE).trans (le_max_left _ _)
  have hi' : (∫ z in Metric.ball (0 : ℂ) 1,
      ‖coronaDbarDensity (fun l w => spanningSigma d.G Z l (F.f w)) i k z‖ ^ 2) ≤
      A * (volume.real (Metric.ball (0 : ℂ) 1) + max E₀ 0 / 2) := by
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  exact (htrace _ hu).trans (ENNReal.ofReal_le_ofReal
    (by simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left hi' hC.le))

end Yau.Blueprint.V02Proof
