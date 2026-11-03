import Yau.LeafProofs.L10InteriorH2Norm

/-! The complete second-order interior estimate on the frozen coordinate balls. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem elliptic_H2_interior (n s : ℕ) (hn : 0 < n)
    (r R ell A : ℝ) (hr : 0 < r) (hrR : r < R) (hell : 0 < ell) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R, ∀ v : RIdx n → ℝ,
        ell * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, a z i j * v i * v j) →
      (∀ k ≤ s + 1, ∀ z ∈ Metric.ball 0 R, ∀ i j,
        ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A) →
      ∀ u : ComplexVector n → ℂ, ContDiffOn ℝ ∞ u (Metric.ball 0 R) →
      (∀ k ≤ s + 2, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      (∀ k ≤ s, IntegrableOn (fun z => ‖iteratedFDeriv ℝ k (LeafCandidates.ellipticOp a b u) z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      LeafCandidates.sobolevNormSq (Metric.ball 0 r) u 2 ≤
        C * ((∫ z in Metric.ball 0 R, ‖u z‖^2 ∂lebesgueC n) +
          ∫ z in Metric.ball 0 R, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n) := by
  let ρ : ℝ := (r + R) / 2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith
  have hρR : ρ < R := by dsimp only [ρ]; linarith
  have hρ : 0 < ρ := hr.trans hrρ
  obtain ⟨C1, hC1, hGrad⟩ := elliptic_caccioppoli_constant n s hn ρ R ell A hρ hρR hell hA
  obtain ⟨C2, hC2, hHess⟩ := elliptic_hessian_interior_constant n s hn r ρ ell A hr hrρ hell hA
  let C : ℝ := 1 + C1 + C2 * (C1 + 1)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a b ha hEll hbound u hu hi hF
  have hsubρ : Metric.ball (0 : ComplexVector n) ρ ⊆ Metric.ball 0 R := Metric.ball_subset_ball hρR.le
  have hsubr : Metric.ball (0 : ComplexVector n) r ⊆ Metric.ball 0 ρ := Metric.ball_subset_ball hrρ.le
  have hsubrR := hsubr.trans hsubρ
  have hG := hGrad a b ha hEll hbound u hu hi hF
  have hH := hHess a b (fun i j => (ha i j).mono hsubρ)
    (fun z hz => hEll z (hsubρ hz))
    (fun k hk z hz i j => hbound k hk z (hsubρ hz) i j) u (hu.mono hsubρ)
    (fun k hk => (hi k hk).mono_set hsubρ) (fun k hk => (hF k hk).mono_set hsubρ)
  have hu0 : IntegrableOn (fun z => ‖u z‖^2) (Metric.ball 0 R) (lebesgueC n) := by
    simpa only [norm_iteratedFDeriv_zero] using hi 0 (by omega)
  have hF0 : IntegrableOn (fun z => ‖LeafCandidates.ellipticOp a b u z‖^2)
      (Metric.ball 0 R) (lebesgueC n) := by
    simpa only [norm_iteratedFDeriv_zero] using hF 0 (Nat.zero_le s)
  have hFn : 0 ≤ ∫ z in Metric.ball 0 R, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n :=
    integral_nonneg fun _ => sq_nonneg _
  have hUn : 0 ≤ ∫ z in Metric.ball 0 R, ‖u z‖^2 ∂lebesgueC n :=
    integral_nonneg fun _ => sq_nonneg _
  have hFmono : (∫ z in Metric.ball 0 ρ, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n) ≤
      ∫ z in Metric.ball 0 R, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n := by
    exact setIntegral_mono_set hF0 (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun z hz => hsubρ hz)
  have hUmono : (∫ z in Metric.ball 0 r, ‖u z‖^2 ∂lebesgueC n) ≤
      ∫ z in Metric.ball 0 R, ‖u z‖^2 ∂lebesgueC n := by
    exact setIntegral_mono_set hu0 (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun z hz => hsubrR hz)
  have hGmono : (∫ z in Metric.ball 0 r, ellipticGradientEnergy u z ∂lebesgueC n) ≤
      ∫ z in Metric.ball 0 ρ, ellipticGradientEnergy u z ∂lebesgueC n := by
    exact setIntegral_mono_set
      (ellipticGradientEnergy_integrableOn Metric.isOpen_ball (hu.mono hsubρ)
        ((hi 1 (by omega)).mono_set hsubρ))
      (Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun z hz => hsubr hz)
  have hNorm := sobolevNormSq_two_le_ellipticEnergy Metric.isOpen_ball (hu.mono hsubrR)
    (fun k hk => (hi k (by omega)).mono_set hsubrR)
  have hHbound : (∫ z in Metric.ball 0 r, ellipticHessianEnergy u z ∂lebesgueC n) ≤
      C2 * (C1 + 1) * ((∫ z in Metric.ball 0 R, ‖u z‖^2 ∂lebesgueC n) +
        ∫ z in Metric.ball 0 R, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n) := by
    nlinarith [mul_nonneg hC2.le (sub_nonneg.mpr hG),
      mul_nonneg hC2.le (sub_nonneg.mpr hFmono), mul_nonneg hC2.le hUn]
  dsimp only [C]
  nlinarith

end Yau.LeafProofs
