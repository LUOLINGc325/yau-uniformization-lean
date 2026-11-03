import Yau.Proofs.D03ClosureSubmoduleMetric

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter Bundle

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem closure_weighted_radius_mono (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (b : Section E) {ρ τ : ℝ} (h : ρ ≤ τ) (σ : ℝ) :
    weightedSectionIntegral E c k b ρ σ ≤ weightedSectionIntegral E c k b τ σ :=
  lintegral_mono_set (discSectionDomain_mono c h)

theorem closure_weighted_exponent_mono (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (b : Section E) (ρ : ℝ) {σ ε : ℝ} (h : σ ≤ ε) :
    weightedSectionIntegral E c k b ρ σ ≤ weightedSectionIntegral E c k b ρ ε := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (hermitianNormSq_nonneg _ _)
  exact Real.rpow_le_rpow_of_exponent_ge (B01Aux.disc_mem c hc x).1
    (B01Aux.disc_mem c hc x).2.le (neg_le_neg h)

theorem closure_weighted_integrand_aemeasurable (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (b : Section E) (ρ σ : ℝ) (hb : HolomorphicSectionOn (r := r) E b (discSectionDomain c ρ)) :
    AEMeasurable (fun x => ENNReal.ofReal (hermitianNormSq (k x) (b x) * ‖c x‖ ^ (-σ)))
      ((BundlePresentation.discArea c).restrict (discSectionDomain c ρ)) := by
  have hn := closure_sectionNormSq_continuousOn E k hk b (discSectionDomain_isOpen c hc ρ) hb
  have hw : Continuous (fun x : M.Carrier => ‖c x‖ ^ (-σ)) :=
    (B01Aux.disc_continuous c hc).norm.rpow_const
      (fun x => Or.inl (B01Aux.disc_mem c hc x).1.ne')
  exact (ENNReal.continuous_ofReal.comp_continuousOn (hn.mul hw.continuousOn)).aemeasurable
    (discSectionDomain_isOpen c hc ρ).measurableSet

theorem closure_weighted_add_le (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (hk : BundleDbar.SmoothMetric (r := r) E k)
    (b d : Section E) (ρ σ : ℝ) (hb : HolomorphicSectionOn (r := r) E b (discSectionDomain c ρ)) :
    weightedSectionIntegral E c k (fun x => b x + d x) ρ σ ≤
      2 * weightedSectionIntegral E c k b ρ σ + 2 * weightedSectionIntegral E c k d ρ σ := by
  have hm := closure_weighted_integrand_aemeasurable E c hc k hk b ρ σ hb
  unfold weightedSectionIntegral
  calc
    _ ≤ ∫⁻ x in discSectionDomain c ρ,
        (2 : ℝ≥0∞) * ENNReal.ofReal (hermitianNormSq (k x) (b x) * ‖c x‖ ^ (-σ)) +
        2 * ENNReal.ofReal (hermitianNormSq (k x) (d x) * ‖c x‖ ^ (-σ)) ∂BundlePresentation.discArea c := by
      apply lintegral_mono
      intro x
      have hw : 0 ≤ ‖c x‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
      calc
        _ ≤ ENNReal.ofReal ((2 * hermitianNormSq (k x) (b x) +
            2 * hermitianNormSq (k x) (d x)) * ‖c x‖ ^ (-σ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (closure_normSq_add_le _ _ _) hw)
        _ = _ := by
          rw [add_mul, ENNReal.ofReal_add
            (mul_nonneg (mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _)) hw)
            (mul_nonneg (mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _)) hw)]
          simp only [mul_assoc, ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat]
    _ = _ := by
      rw [lintegral_add_left' (hm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num)]
      rfl

theorem closure_weighted_smul_le (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (b : Section E) (ρ σ B : ℝ) (hB : 0 ≤ B)
    (f : M.Carrier → ℂ) (hf : ∀ x ∈ discSectionDomain c ρ, ‖f x‖ ≤ B) :
    weightedSectionIntegral E c k (fun x => f x • b x) ρ σ ≤
      ENNReal.ofReal (B ^ 2) * weightedSectionIntegral E c k b ρ σ := by
  unfold weightedSectionIntegral
  calc
    _ ≤ ∫⁻ x in discSectionDomain c ρ,
        ENNReal.ofReal (B ^ 2 * (hermitianNormSq (k x) (b x) * ‖c x‖ ^ (-σ))) ∂BundlePresentation.discArea c := by
      apply setLIntegral_mono' (discSectionDomain_isOpen c hc ρ).measurableSet
      intro x hx
      rw [closure_normSq_smul]
      apply ENNReal.ofReal_le_ofReal
      have hp := pow_le_pow_left₀ (norm_nonneg (f x)) (hf x hx) 2
      nlinarith [mul_nonneg (hermitianNormSq_nonneg (k x) (b x))
        (Real.rpow_nonneg (norm_nonneg (c x)) (-σ))]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (sq_nonneg B)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

theorem closure_weighted_zero (c : DiscCoordinate M) (k : BundleDbar.Metric E) (ρ σ : ℝ) :
    weightedSectionIntegral E c k (fun _ => 0) ρ σ = 0 := by
  simp [weightedSectionIntegral, closure_normSq_zero]

end Yau.Proofs.D03Aux
