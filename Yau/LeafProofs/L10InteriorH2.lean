import Yau.LeafProofs.L10InteriorHessianEnergy

/-! Nested-ball second-order estimates with constants selected before the coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem elliptic_hessian_interior_constant (n s : ℕ) (hn : 0 < n)
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
      (∫ z in Metric.ball 0 r, ellipticHessianEnergy u z ∂lebesgueC n) ≤
        C * ((∫ z in Metric.ball 0 R, ellipticGradientEnergy u z ∂lebesgueC n) +
          ∫ z in Metric.ball 0 R, ‖LeafCandidates.ellipticOp a b u z‖^2 ∂lebesgueC n) := by
  obtain ⟨η, M, hM, hη, hcη, hsη, hηBound, hηDeriv, hηNear⟩ :=
    exists_elliptic_cutoff n hr hrR
  let B : ℝ := (2 * n + 1) * A
  let C : ℝ := 2 * ellipticHessianAbsorptionConstant (Fintype.card (RIdx n)) ell A B M / ell
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos (mul_pos (by norm_num)
      (ellipticHessianAbsorptionConstant_pos (by positivity) hell hA.le hB.le hM.le)) hell
  refine ⟨C, hC, ?_⟩
  intro a b ha hEll hbound u hu hi hF
  have hco (z : ComplexVector n) (hz : z ∈ Metric.ball 0 R) :=
    elliptic_original_coefficient_bounds hn hbound hz
  have hu1 := hi 1 (by omega)
  have hu2 := hi 2 (by omega)
  have hF0 : IntegrableOn (fun z => ‖LeafCandidates.ellipticOp a b u z‖^2)
      (Metric.ball 0 R) (lebesgueC n) := by
    simpa only [norm_iteratedFDeriv_zero] using hF 0 (Nat.zero_le s)
  have hWeighted := elliptic_hessian_weighted Metric.isOpen_ball hell hA.le hB.le hM.le
    ha hu hη hcη hsη hηBound hηDeriv hEll (fun z hz => (hco z hz).1)
    (fun z hz k i j => (hco z hz).2.2.1 i j k)
    (fun z hz => (hco z hz).2.2.2) hu1 hu2 hF0
  calc
    _ = ∫ z in Metric.ball 0 r, (η z)^2 * ellipticHessianEnergy u z ∂lebesgueC n := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change ellipticHessianEnergy u z = (η z)^2 * ellipticHessianEnergy u z
      rw [(hηNear z hz).eq_of_nhds]
      simp
    _ ≤ ∫ z in Metric.ball 0 R, (η z)^2 * ellipticHessianEnergy u z ∂lebesgueC n := by
      apply setIntegral_mono_set
        (ellipticHessianEnergy_weighted_integrableOn Metric.isOpen_ball hu hη hηBound hu2)
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _))
      exact Filter.Eventually.of_forall fun z hz => Metric.ball_subset_ball hrR.le hz
    _ ≤ _ := hWeighted

end Yau.LeafProofs
