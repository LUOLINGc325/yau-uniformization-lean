import Yau.LeafProofs.L14TwoL2
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hsub : K ⊆ localDomain (r := r) E a) (p : TwoCoefficientIndex n r)

def weightedTwoLocalCoefficient (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (locallyL2_coefficients_memLp E u.1 u.2.1 a ![p.1.2,p.2] p.1.1 K hK hsub).toLp
    (fun z => coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1)

theorem weightedTwoLocalCoefficient_ae (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u =ᵐ[(lebesgueC n).restrict K]
      (fun z => coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1) := MemLp.coeFn_toLp _

def weightedTwoLocalCoefficientLinear :
    WeightedTwoSection E g μ hμ h hh φ hφ →ₗ[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) where
  toFun := weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
  map_add' u v := by
    apply Lp.ext
    filter_upwards [weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p (u+v),
      weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p u,
      weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p v,
      Lp.coeFn_add (weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u)
        (weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p v)] with z huv hu hv hadd
    rw [huv, hadd, Pi.add_apply, hu, hv]
    exact coefficients_add E u.1 v.1 a z ![p.1.2,p.2] p.1.1
  map_smul' c u := by
    change weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p (c • u) =
      c • weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u
    apply Lp.ext
    filter_upwards [weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p (c • u),
      weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p u,
      Lp.coeFn_smul c (weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u)] with z hcu hu hsmul
    rw [hcu, hsmul, Pi.smul_apply, hu]
    exact coefficients_smul E c u.1 a z ![p.1.2,p.2] p.1.1

theorem weightedTwoLocalCoefficient_norm_sq (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    ‖weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u‖ ^ 2 =
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1‖ ^ 2) ∂lebesgueC n).toReal :=
  complex_toLp_norm_sq _ _ _

theorem weightedTwoLocalCoefficient_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : WeightedTwoSection E g μ hμ h hh φ hφ,
      ‖weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := compact_two_coefficient_integral_bound E g μ hμ h hh φ hφ a K hK hsub p
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro u
  have hfin : ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ φ u.1 < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top u.2.2
  have hs : ‖weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
    rw [weightedTwoLocalCoefficient_norm_sq E g μ hμ h hh φ hφ a K hK hsub p]
    have ht := ENNReal.toReal_mono hfin.ne (hb u.1 u.2.1)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at ht
    have hn := weightedTwoSection_norm_sq E g μ hμ h hh φ hφ u
    change ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal at hn
    rwa [hn]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg u))).mp
  calc
    _ ≤ C * ‖u‖ ^ 2 := hs
    _ = (Real.sqrt C * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hC]

def weightedTwoLocalCoefficientCLM :
    WeightedTwoSection E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (weightedTwoLocalCoefficientLinear E g μ hμ h hh φ hφ a K hK hsub p).mkContinuousOfExistsBound
    (by
      obtain ⟨C, _, hC⟩ := weightedTwoLocalCoefficient_bounded E g μ hμ h hh φ hφ a K hK hsub p
      exact ⟨C, hC⟩)

theorem weightedTwoLocalCoefficientCLM_apply (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoLocalCoefficientCLM E g μ hμ h hh φ hφ a K hK hsub p u =
      weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u := rfl

/-- The local coefficient of a computed weighted Hilbert element is obtained
by extending the actual coefficient map into the complete local L² space. -/
def weightedTwoHilbertLocalCoefficient :
    WeightedTwoHilbert E g μ hμ h hh φ hφ →L[ℂ] Lp ℂ 2 ((lebesgueC n).restrict K) :=
  (weightedTwoLocalCoefficientCLM E g μ hμ h hh φ hφ a K hK hsub p).fromCompletion

theorem weightedTwoHilbertLocalCoefficient_realize (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ u) =
        weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem weightedTwoHilbertLocalCoefficient_realize_ae (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ u) =ᵐ[(lebesgueC n).restrict K]
        (fun z => coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1) := by
  rw [weightedTwoHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hsub p]
  exact weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p u


theorem weightedTwoHilbertLocalCoefficient_restrict
    (K' : Set (ComplexVector n)) (hK' : IsCompact K')
    (hsub' : K' ⊆ localDomain (r := r) E a) (hKK' : K ⊆ K')
    (u : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp)
      (show (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' from
        by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n)))
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p u) =
        weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u := by
  let hmeasure : (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' :=
    by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n))
  let T := Lp.LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
  change T (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p u) =
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (T.continuous.comp (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p).continuous)
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p).continuous) ?_
  intro v
  change T (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ v)) =
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ v)
  rw [weightedTwoHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K' hK' hsub' p,
    weightedTwoHilbertLocalCoefficient_realize E g μ hμ h hh φ hφ a K hK hsub p]
  apply Lp.ext
  have hbig := (weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K' hK' hsub' p v).filter_mono
    (ae_mono (Measure.restrict_mono hKK' (le_refl (lebesgueC n))))
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
      (weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p v), hbig,
    weightedTwoLocalCoefficient_ae E g μ hμ h hh φ hφ a K hK hsub p v] with z ht hb hs
  exact ht.trans (hb.trans hs.symm)

theorem weightedTwoHilbertLocalCoefficient_ae_restrict
    (K' : Set (ComplexVector n)) (hK' : IsCompact K')
    (hsub' : K' ⊆ localDomain (r := r) E a) (hKK' : K ⊆ K')
    (u : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p u =ᵐ[(lebesgueC n).restrict K]
      weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hsub p u := by
  let hmeasure : (lebesgueC n).restrict K ≤ (1 : ℝ≥0∞) • (lebesgueC n).restrict K' :=
    by simpa only [one_smul] using Measure.restrict_mono hKK' (le_refl (lebesgueC n))
  have hcoe := Lp.coeFn_LpToLpOfMeasureLeSMul (E := ℂ) (p := 2) (c := 1) (by simp) hmeasure
    (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K' hK' hsub' p u)
  rw [weightedTwoHilbertLocalCoefficient_restrict E g μ hμ h hh φ hφ a K hK hsub p K' hK' hsub' hKK' u] at hcoe
  exact hcoe.symm


end Yau.LeafProofs.L14Aux
