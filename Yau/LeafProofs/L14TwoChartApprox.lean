import Yau.LeafProofs.L14TwoLocalize
import Yau.LeafProofs.L14TwoLocalSymbols
import Yau.LeafProofs.L14CompactLpFields
import Yau.LeafProofs.L14AlternatingPairSystem

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weightedNormSq_two_le_model_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a : M.Carrier)
    (u : NQForm E 2) (hu : LocallyL2 (r := r) E u)
    (hz : ∀ x, x ∉ bundleChartSource (r := r) E a → u x = (0 : NQForm E 2) x)
    (e : ComplexVector n → TwoCoefficientIndex n r → ℂ)
    (he : ∀ c, MemLp (fun z => e z c) 2 (lebesgueC n))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ localDomain (r := r) E a,
      chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z)) ≤
        C * ∑ c, ‖e z c‖ ^ 2) :
    weightedNormSq (r := r) E g.form h μ φ u ≤
      ENNReal.ofReal (((2 : ℝ) ^ n * C) * ∑ c, ∫ z, ‖e z c‖ ^ 2 ∂lebesgueC n) := by
  have hi (c : TwoCoefficientIndex n r) : Integrable (fun z => ‖e z c‖ ^ 2) (lebesgueC n) :=
    (memLp_two_iff_integrable_sq_norm (he c).aestronglyMeasurable).mp (he c)
  have his : Integrable (fun z => ∑ c, ‖e z c‖ ^ 2) (lebesgueC n) :=
    integrable_finsetSum _ (fun c _ => hi c)
  have hn (z : ComplexVector n) : 0 ≤ ∑ c, ‖e z c‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : Function.support (fun x => ENNReal.ofReal
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) ⊆ bundleChartSource (r := r) E a := by
    intro x hx
    by_contra hnx
    apply hx
    change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) = 0
    rw [formNormSq_congr_at E g.form h u (0 : NQForm E 2) x (hz x hnx), formNormSq_zero, zero_mul,
      ENNReal.ofReal_zero]
  calc
    _ = ∫⁻ x in bundleChartSource (r := r) E a, ENNReal.ofReal
        (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ :=
      (setLIntegral_eq_of_support_subset hs).symm
    _ = ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n :=
      weighted_two_chart_integral_rough E g μ hμ h hh φ hφ u hu a
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (C * ∑ c, ‖e z c‖ ^ 2) ∂lebesgueC n := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
      exact ENNReal.ofReal_le_ofReal (hbound z hz)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z,
        ENNReal.ofReal (C * ∑ c, ‖e z c‖ ^ 2) ∂lebesgueC n := mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hC]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal his (Eventually.of_forall hn),
        integral_finsetSum Finset.univ (fun c _ => hi c),
        ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n),
        ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) hC)]


variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedTwoSection_norm_le_compact_coefficients
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : WeightedTwoSection E g μ hμ h hh φ hφ,
      (∀ x, x ∉ bundleChartSource (r := r) E a → u.1 x = (0 : NQForm E 2) x) →
      (∀ z ∈ localDomain (r := r) E a, z ∉ K → ∀ p : TwoCoefficientIndex n r,
        coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1 = 0) →
      ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ u‖ ^ 2 ≤
        C * ∑ p, ‖weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p u‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := compact_two_coefficient_norm_upper_bound E g h hh φ hφ a K hK hKO
  refine ⟨(2 : ℝ) ^ n * C, mul_nonneg (pow_nonneg (by norm_num) _) hC, ?_⟩
  intro u hz hcoeffzero
  let e := fun z (p : TwoCoefficientIndex n r) => K.indicator
    (fun z => coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1) z
  have he (p : TwoCoefficientIndex n r) : MemLp (fun z => e z p) 2 (lebesgueC n) :=
    (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr
      (locallyL2_coefficients_memLp E u.1 u.2.1 a ![p.1.2,p.2] p.1.1 K hK hKO)
  have hb : ∀ z ∈ localDomain (r := r) E a,
      chartTwoCoefficientNormSq (r := r) E g.form h u.1 a z * Real.exp (-φ (chartInv a z)) ≤
        C * ∑ p, ‖e z p‖ ^ 2 := by
    intro z hzo
    by_cases hzK : z ∈ K
    · simpa only [e, Set.indicator_of_mem hzK] using hbound u.1 z hzK
    · have hzero := hcoeffzero z hzo hzK
      simp only [chartTwoCoefficientNormSq, dotProduct, Matrix.mulVec, Pi.star_apply,
        hzero, e, Set.indicator_of_notMem hzK, star_zero, zero_mul, Finset.sum_const_zero,
        Complex.zero_re, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  have hle := weightedNormSq_two_le_model_integral E g μ hμ h hh φ hφ a u.1 u.2.1 hz e he C hC hb
  have hei (p : TwoCoefficientIndex n r) :
      ∫ z, ‖e z p‖ ^ 2 ∂lebesgueC n =
        ‖weightedTwoLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p u‖ ^ 2 := by
    rw [weightedTwoLocalCoefficient_norm_sq]
    have hi := (memLp_two_iff_integrable_sq_norm (he p).aestronglyMeasurable).mp (he p)
    have heq : (fun z => ‖e z p‖ ^ 2) = K.indicator
        (fun z => ‖coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1‖ ^ 2) := by
      funext z
      by_cases hzK : z ∈ K <;> simp [e, hzK]
    have hen : (∫ z, ‖e z p‖ ^ 2 ∂lebesgueC n) =
        (∫⁻ z, ENNReal.ofReal (‖e z p‖ ^ 2) ∂lebesgueC n).toReal := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z => sq_nonneg _),
        ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg _)]
    rw [hen]
    congr 1
    simp_rw [congrFun heq]
    have heq' : (fun z => ENNReal.ofReal
        (K.indicator (fun z => ‖coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1‖ ^ 2) z)) =
        K.indicator (fun z => ENNReal.ofReal (‖coefficients (r := r) E u.1 a z ![p.1.2,p.2] p.1.1‖ ^ 2)) := by
      funext z
      by_cases hzK : z ∈ K <;> simp [hzK]
    rw [heq', lintegral_indicator hK.measurableSet]
  simp_rw [hei] at hle
  rw [realizeWeightedTwoSection_norm_sq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hC)
      (Finset.sum_nonneg fun p _ => sq_nonneg _)))

/-- A compact chart controls the norm of a cutoff of every completed two-form. -/
theorem weightedTwoCutoff_sub_norm_le_local_coefficients
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hKχ : tsupport (L18Aux.chartPullbackZero a χ) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
      (V : WeightedTwoSection E g μ hμ h hh φ hφ),
      (∀ x, x ∉ bundleChartSource (r := r) E a → V.1 x = (0 : NQForm E 2) x) →
      (∀ z ∈ localDomain (r := r) E a, z ∉ K → ∀ p : TwoCoefficientIndex n r,
        coefficients (r := r) E V.1 a z ![p.1.2,p.2] p.1.1 = 0) →
      ‖weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W -
        realizeWeightedTwoSection E g μ hμ h hh φ hφ V‖ ^ 2 ≤
      C * ∑ p, ‖weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W) -
          weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p
            (realizeWeightedTwoSection E g μ hμ h hh φ hφ V)‖ ^ 2 := by
  obtain ⟨C, hC, hnorm⟩ := weightedTwoSection_norm_le_compact_coefficients E g μ hμ h hh φ hφ a K hK hKO
  refine ⟨C, hC, ?_⟩
  intro W V hV hVc
  induction W using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih U =>
    change ‖weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ U) -
      realizeWeightedTwoSection E g μ hμ h hh φ hφ V‖ ^ 2 ≤ _
    rw [weightedTwoCutoff_realize, ← realizeWeightedTwoSection_sub]
    let D := weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hboundχ U - V
    have hz : ∀ x, x ∉ bundleChartSource (r := r) E a → D.1 x = (0 : NQForm E 2) x := by
      intro x hx
      have hχz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hsχ hs))
      have hd := WeightedTwoSection.toForm_sub E g μ hμ h hh φ hφ
        (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hboundχ U) V
      change D.1 = multiplyForm E (fun x => (χ x : ℂ)) U.1 - V.1 at hd
      rw [hd]
      apply Subtype.ext
      change (χ x : ℂ) • (U.1 x).1 - (V.1 x).1 = 0
      have hv := congrArg Subtype.val (hV x hx)
      change (V.1 x).1 = 0 at hv
      rw [hχz, Complex.ofReal_zero, zero_smul, hv, sub_zero]
    have hzc : ∀ z ∈ localDomain (r := r) E a, z ∉ K → ∀ p : TwoCoefficientIndex n r,
        coefficients (r := r) E D.1 a z ![p.1.2,p.2] p.1.1 = 0 := by
      intro z hz hn p
      have hpull : L18Aux.chartPullbackZero a χ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs => hn (hKχ hs))
      have hχz : χ (chartInv a z) = 0 := by
        simpa only [L18Aux.chartPullbackZero, ite_eq_left hz.1] using hpull
      have hd := WeightedTwoSection.toForm_sub E g μ hμ h hh φ hφ
        (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hboundχ U) V
      change D.1 = multiplyForm E (fun x => (χ x : ℂ)) U.1 - V.1 at hd
      rw [hd, coefficients_sub]
      change coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) U.1) a z ![p.1.2,p.2] p.1.1 - _ = _
      rw [coefficients_multiplyForm, hχz, Complex.ofReal_zero, zero_mul, hVc z hz hn p, sub_zero]
    have hn := hnorm D hz hzc
    change ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ D‖ ^ 2 ≤ _
    convert hn using 1
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    change ‖weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ U)) -
      weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ V)‖ = _
    rw [weightedTwoCutoff_realize, weightedTwoHilbertLocalCoefficient_realize,
      weightedTwoHilbertLocalCoefficient_realize]
    congr 1
    exact (map_sub (weightedTwoLocalCoefficientLinear E g μ hμ h hh φ hφ a K hK hKO p)
      (weightedTwoCutoffSection E g μ hμ h hh φ hφ χ hχ hboundχ U) V).symm

/-- An ordinary model error dominates the error between its local L² classes. -/
theorem localLp_sub_norm_sq_le_compact_error
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (K : Set X) (hK : MeasurableSet K)
    (u v : Lp ℂ 2 (ν.restrict K)) (f : X → ℂ)
    (hu : u =ᵐ[ν.restrict K] f)
    (he : MemLp (fun x => f x - compactLpField ν K v x) 2 ν) :
    ‖u - v‖ ^ 2 ≤ ∫ x, ‖f x - compactLpField ν K v x‖ ^ 2 ∂ν := by
  let e := fun x => f x - compactLpField ν K v x
  have heK : MemLp e 2 (ν.restrict K) := he.mono_measure Measure.restrict_le_self
  have heq : heK.toLp e = u - v := by
    apply Lp.ext
    filter_upwards [heK.coeFn_toLp, hu, compactLpField_ae_restrict ν K hK v,
      Lp.coeFn_sub u v] with x hx hux hvx hsub
    rw [hx, hsub]
    change f x - compactLpField ν K v x = u x - v x
    rw [hux, hvx]
  rw [← heq, complex_toLp_norm_sq]
  have hi := (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  have hfin : (∫⁻ x, ENNReal.ofReal (‖e x‖ ^ 2) ∂ν) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  calc
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖e x‖ ^ 2) ∂ν).toReal :=
      ENNReal.toReal_mono hfin (setLIntegral_le_lintegral _ _)
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _),
        ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]

/-- Fixed-compact coefficient convergence reconstructs the actual cutoff of any
completed weighted two-form. -/
theorem weightedTwoChartSection_tendsto_cutoff_of_model_errors
    (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hKχ : tsupport (L18Aux.chartPullbackZero a χ) ⊆ K)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (F : ℕ → ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ j z i k, F j z k i = -F j z i k)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hsF : ∀ j, tsupport (F j) ⊆ K)
    (he : ∀ j (p : TwoCoefficientIndex n r), MemLp
      (fun z => F j z p.1.2 p.2 p.1.1 - compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W) z p) 2 (lebesgueC n))
    (ht : ∀ p : TwoCoefficientIndex n r, Tendsto (fun j => ∫ z,
      ‖F j z p.1.2 p.2 p.1.1 - compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W) z p‖ ^ 2 ∂lebesgueC n)
      atTop (𝓝 0)) :
    Tendsto (fun j => realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (weightedTwoChartSection E g μ hμ h hh φ hφ hE a (F j) (hskew j) (hF j)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)))
      atTop (𝓝 (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W)) := by
  classical
  let T := weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W
  let U := fun j => weightedTwoChartSection E g μ hμ h hh φ hφ hE a (F j) (hskew j) (hF j)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)
  obtain ⟨C, hC, hnorm⟩ := weightedTwoCutoff_sub_norm_le_local_coefficients E g μ hμ h hh φ hφ
    a K hK hKO χ hχ hboundχ hsχ hKχ
  have hsq (j : ℕ) : ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ (U j) - T‖ ^ 2 ≤
      C * ∑ p : TwoCoefficientIndex n r, ∫ z,
        ‖F j z p.1.2 p.2 p.1.1 - compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO T z p‖ ^ 2 ∂lebesgueC n := by
    have hz : ∀ x, x ∉ bundleChartSource (r := r) E a → (U j).1 x = (0 : NQForm E 2) x := by
      intro x hx
      change twoFormPushforward (r := r) E a (F j) x = _
      simp only [twoFormPushforward, dite_eq_right hx]
      rfl
    have hzc : ∀ z ∈ localDomain (r := r) E a, z ∉ K → ∀ p : TwoCoefficientIndex n r,
        coefficients (r := r) E (U j).1 a z ![p.1.2,p.2] p.1.1 = 0 := by
      intro z hz hn p
      change coefficients (r := r) E (twoFormPushforward (r := r) E a (F j)) a z ![p.1.2,p.2] p.1.1 = _
      rw [twoFormPushforward_coefficients E a (F j) (hskew j) z hz]
      have hfz : F j z = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hn (hsF j hs))
      simp only [hfz, Pi.zero_apply, PiLp.zero_apply]
    have hn := hnorm W (U j) hz hzc
    rw [norm_sub_rev] at hn
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Finset.sum_le_sum
    intro p _
    rw [norm_sub_rev]
    apply localLp_sub_norm_sq_le_compact_error (lebesgueC n) K hK.measurableSet
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p
        (realizeWeightedTwoSection E g μ hμ h hh φ hφ (U j)))
      (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p T)
      (fun z => F j z p.1.2 p.2 p.1.1) _ (he j p)
    apply (weightedTwoHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ a K hK hKO p (U j)).trans
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact twoFormPushforward_coefficients E a (F j) (hskew j) z (hKO hz) p.1.2 p.2 p.1.1
  have hpow : Tendsto (fun j => ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ (U j) - T‖ ^ 2)
      atTop (𝓝 0) := squeeze_zero (fun j => sq_nonneg _) hsq (by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finsetSum Finset.univ (fun p _ => ht p)).const_mul C)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hpow
  simp only [Real.sqrt_zero] at hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hn using 1
  funext j
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem complex_half_sub_norm_sq_le (a b : ℂ) :
    ‖(1 / 2 : ℂ) * (a - b)‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have ht := norm_sub_le a b
  have hs : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
  norm_num [norm_mul, norm_div] at *
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Antisymmetrization preserves strong coefficient convergence to an a.e.
alternating field. -/
theorem alternatingTwoModel_errors
    (G : ComplexVector n → TwoCoefficientIndex n r → ℂ)
    (hG : ∀ i j : Fin n, ∀ α : Fin r,
      (fun z => G z ((α,j),i)) =ᵐ[lebesgueC n] (fun z => -G z ((α,i),j)))
    (F : ℕ → ComplexVector n → Fin n → Fin n → ComplexVector r)
    (he : ∀ j (p : TwoCoefficientIndex n r), MemLp
      (fun z => F j z p.1.2 p.2 p.1.1 - G z p) 2 (lebesgueC n))
    (ht : ∀ p : TwoCoefficientIndex n r, Tendsto
      (fun j => ∫ z, ‖F j z p.1.2 p.2 p.1.1 - G z p‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) :
    (∀ j (p : TwoCoefficientIndex n r), MemLp
      (fun z => alternatingTwoModel (F j) z p.1.2 p.2 p.1.1 - G z p) 2 (lebesgueC n)) ∧
    (∀ p : TwoCoefficientIndex n r, Tendsto
      (fun j => ∫ z, ‖alternatingTwoModel (F j) z p.1.2 p.2 p.1.1 - G z p‖ ^ 2 ∂lebesgueC n)
      atTop (𝓝 0)) := by
  let e := fun j z (p : TwoCoefficientIndex n r) => F j z p.1.2 p.2 p.1.1 - G z p
  have hproj (j : ℕ) (p : TwoCoefficientIndex n r) :
      (fun z => alternatingTwoModel (F j) z p.1.2 p.2 p.1.1 - G z p) =ᵐ[lebesgueC n]
        (fun z => (1 / 2 : ℂ) * (e j z p - e j z ((p.1.1,p.2),p.1.2))) := by
    filter_upwards [hG p.1.2 p.2 p.1.1] with z hz
    simp only [alternatingTwoModel_apply, e, hz]
    ring
  have hmem (j : ℕ) (p : TwoCoefficientIndex n r) : MemLp
      (fun z => alternatingTwoModel (F j) z p.1.2 p.2 p.1.1 - G z p) 2 (lebesgueC n) :=
    (((he j p).sub (he j ((p.1.1,p.2),p.1.2))).const_mul (1 / 2 : ℂ)).ae_eq (hproj j p).symm
  refine ⟨hmem, ?_⟩
  intro p
  have hbound (j : ℕ) :
      (∫ z, ‖alternatingTwoModel (F j) z p.1.2 p.2 p.1.1 - G z p‖ ^ 2 ∂lebesgueC n) ≤
      (∫ z, ‖e j z p‖ ^ 2 ∂lebesgueC n) +
        ∫ z, ‖e j z ((p.1.1,p.2),p.1.2)‖ ^ 2 ∂lebesgueC n := by
    have hi (q : TwoCoefficientIndex n r) : Integrable (fun z => ‖e j z q‖ ^ 2) (lebesgueC n) :=
      (memLp_two_iff_integrable_sq_norm (he j q).aestronglyMeasurable).mp (he j q)
    rw [← integral_add (hi p) (hi ((p.1.1,p.2),p.1.2))]
    apply integral_mono_ae
      ((memLp_two_iff_integrable_sq_norm (hmem j p).aestronglyMeasurable).mp (hmem j p))
      ((hi p).add (hi ((p.1.1,p.2),p.1.2)))
    filter_upwards [hproj j p] with z hz
    rw [hz]
    exact complex_half_sub_norm_sq_le _ _
  exact squeeze_zero (fun j => integral_nonneg fun z => sq_nonneg _) hbound
    (by simpa only [add_zero] using (ht p).add (ht ((p.1.1,p.2),p.1.2)))

/-- Smooth alternating projections of model approximants converge strongly to
the actual cutoff of every completed weighted two-form. -/
theorem weightedTwoAlternatingChartSection_tendsto_cutoff_of_model_errors
    (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hboundχ : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hsχ : tsupport χ ⊆ bundleChartSource (r := r) E a)
    (hKχ : tsupport (L18Aux.chartPullbackZero a χ) ⊆ K)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (F : ℕ → ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (hsF : ∀ j, tsupport (F j) ⊆ K)
    (he : ∀ j (p : TwoCoefficientIndex n r), MemLp
      (fun z => F j z p.1.2 p.2 p.1.1 - compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W) z p) 2 (lebesgueC n))
    (ht : ∀ p : TwoCoefficientIndex n r, Tendsto (fun j => ∫ z,
      ‖F j z p.1.2 p.2 p.1.1 - compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
        (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W) z p‖ ^ 2 ∂lebesgueC n)
      atTop (𝓝 0)) :
    let hAlt := fun j => alternatingTwoModel_properties (F j) (hF j)
      (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j))
    Tendsto (fun j => realizeWeightedTwoSection E g μ hμ h hh φ hφ
      (weightedTwoChartSection E g μ hμ h hh φ hφ hE a (alternatingTwoModel (F j))
        (alternatingTwoModel_skew (F j)) (hAlt j).1 (hAlt j).2.1
        ((hAlt j).2.2.trans ((hsF j).trans hKO))))
      atTop (𝓝 (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W)) := by
  classical
  dsimp only
  obtain ⟨hmem, hlim⟩ := alternatingTwoModel_errors
    (compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W))
    (compactTwoHilbertField_skew_ae E g μ hμ h hh φ hφ a K hK hKO
      (weightedTwoCutoff E g μ hμ h hh φ hφ χ hχ hboundχ W)) F he ht
  exact weightedTwoChartSection_tendsto_cutoff_of_model_errors E g μ hμ h hh φ hφ hE
    a K hK hKO χ hχ hboundχ hsχ hKχ W (fun j => alternatingTwoModel (F j))
    (fun j => alternatingTwoModel_skew (F j))
    (fun j => (alternatingTwoModel_properties (F j) (hF j)
      (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j))).1)
    (fun j => (alternatingTwoModel_properties (F j) (hF j)
      (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j))).2.2.trans (hsF j)) hmem hlim

end Yau.LeafProofs.L14Aux
