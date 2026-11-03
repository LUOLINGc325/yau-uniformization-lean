import Yau.LeafProofs.L14BundleFriedrichs

noncomputable section
open scoped Topology ContDiff Matrix
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

/-- A finite Hermitian quadratic expression is uniformly bounded by the
ordinary coefficient norm, with no positivity assumption required. -/
theorem matrix_quadratic_re_le_coefficient_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).re ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ‖v i‖ ^ 2 := by
  classical
  let S := ∑ i, ‖v i‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv (i j : ι) : ‖v i‖ * ‖v j‖ ≤ S := by
    have hi : ‖v i‖ ^ 2 ≤ S := Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hj : ‖v j‖ ^ 2 ≤ S := Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖v i‖ - ‖v j‖)]
  have he : star v ⬝ᵥ A *ᵥ v = ∑ i, ∑ j, star (v i) * A i j * v j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  calc
    _ ≤ ‖star v ⬝ᵥ A *ᵥ v‖ := Complex.re_le_norm _
    _ = ‖∑ i, ∑ j, star (v i) * A i j * v j‖ := by rw [he]
    _ ≤ ∑ i, ∑ j, ‖star (v i) * A i j * v j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * S := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_star]
      calc
        _ = ‖A i j‖ * (‖v i‖ * ‖v j‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hv i j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul, S]

/-- Multiplication by a bounded measurable complex coefficient preserves
actual squared-norm L² convergence. -/
theorem integral_sq_tendsto_zero_bounded_complex_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (f : ℕ → X → ℂ) (hf : ∀ j, MemLp (f j) 2 ν)
    (ht : Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂ν) atTop (𝓝 0))
    (c : X → ℂ) (hc : AEStronglyMeasurable c ν) (C : ℝ) (hC : 0 ≤ C)
    (hcC : ∀ x, ‖c x‖ ≤ C) :
    (∀ j, MemLp (fun x => c x * f j x) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖c x * f j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have hm (j : ℕ) : MemLp (fun x => c x * f j x) 2 ν := by
    apply (hf j).of_le_mul (c := C) (hc.mul (hf j).aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖c x * f j x‖ ≤ C * ‖f j x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcC x) (norm_nonneg _)
  refine ⟨hm, ?_⟩
  have hb (j : ℕ) : (∫ x, ‖c x * f j x‖ ^ 2 ∂ν) ≤ C ^ 2 * ∫ x, ‖f j x‖ ^ 2 ∂ν := by
    have hi := (memLp_two_iff_integrable_sq_norm (hf j).aestronglyMeasurable).mp (hf j)
    have hci := (memLp_two_iff_integrable_sq_norm (hm j).aestronglyMeasurable).mp (hm j)
    calc
      _ ≤ ∫ x, C ^ 2 * ‖f j x‖ ^ 2 ∂ν := integral_mono hci (hi.const_mul _) (fun x => by
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hcC x)) (sq_nonneg _))
      _ = _ := integral_const_mul _ _
  exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _) hb (by
    simpa only [mul_zero] using ht.const_mul (C ^ 2))

open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem compact_one_coefficient_norm_upper_bound (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 1) z, z ∈ K →
      chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z)) ≤
        C * ∑ c : Fin n × Fin r, ‖coefficients (r := r) E u a z (fun _ => c.1) c.2‖ ^ 2 := by
  classical
  let B := fun z => (∑ i, ∑ j, ‖chartOneMetricMatrix (r := r) E g.form h a z i j‖) *
    Real.exp (-φ (chartInv a z))
  have hB : ContinuousOn B (localDomain (r := r) E a) := by
    apply ContinuousOn.mul
    · apply continuousOn_finset_sum
      intro i _
      apply continuousOn_finset_sum
      intro j _
      exact ((chartOneMetricMatrix_contDiffOn E g h hh a i j).continuousOn).norm
    · exact Real.continuous_exp.comp_continuousOn (((hφ a).continuousOn.mono Set.inter_subset_left).neg)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hB.mono hKO)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u z hz
  have hS : 0 ≤ ∑ c : Fin n × Fin r, ‖coefficients (r := r) E u a z (fun _ => c.1) c.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : B z ≤ max C 0 := (le_abs_self _).trans
    ((show |B z| ≤ C from hC z hz).trans (le_max_left _ _))
  calc
    _ ≤ ((∑ i, ∑ j, ‖chartOneMetricMatrix (r := r) E g.form h a z i j‖) *
        ∑ c : Fin n × Fin r, ‖coefficients (r := r) E u a z (fun _ => c.1) c.2‖ ^ 2) *
        Real.exp (-φ (chartInv a z)) :=
      mul_le_mul_of_nonneg_right (matrix_quadratic_re_le_coefficient_sq _ _) (Real.exp_pos _).le
    _ = B z * ∑ c : Fin n × Fin r, ‖coefficients (r := r) E u a z (fun _ => c.1) c.2‖ ^ 2 := by dsimp only [B]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hS

theorem weightedNormSq_one_le_model_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a : M.Carrier)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u)
    (hz : ∀ x, x ∉ bundleChartSource (r := r) E a → u x = (0 : NQForm E 1) x)
    (e : ComplexVector n → (Fin n × Fin r) → ℂ)
    (he : ∀ c, MemLp (fun z => e z c) 2 (lebesgueC n))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ localDomain (r := r) E a,
      chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z)) ≤
        C * ∑ c, ‖e z c‖ ^ 2) :
    weightedNormSq (r := r) E g.form h μ φ u ≤
      ENNReal.ofReal (((2 : ℝ) ^ n * C) * ∑ c, ∫ z, ‖e z c‖ ^ 2 ∂lebesgueC n) := by
  have hi (c : Fin n × Fin r) : Integrable (fun z => ‖e z c‖ ^ 2) (lebesgueC n) :=
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
    rw [formNormSq_congr_at E g.form h u (0 : NQForm E 1) x (hz x hnx), formNormSq_zero, zero_mul,
      ENNReal.ofReal_zero]
  calc
    _ = ∫⁻ x in bundleChartSource (r := r) E a, ENNReal.ofReal
        (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ :=
      (setLIntegral_eq_of_support_subset hs).symm
    _ = ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (chartOneCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n :=
      weighted_one_chart_integral E g μ hμ h hh φ hφ u hu a
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

theorem weightedNormSq_one_le_compact_model_errors (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKO : K ⊆ localDomain (r := r) E a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 1), LocallyL2 (r := r) E u →
      (∀ x, x ∉ bundleChartSource (r := r) E a → u x = (0 : NQForm E 1) x) →
      ∀ (e : ComplexVector n → (Fin n × Fin r) → ℂ),
      (∀ c, MemLp (fun z => e z c) 2 (lebesgueC n)) →
      (∀ c, tsupport (fun z => e z c) ⊆ K) →
      (∀ z ∈ localDomain (r := r) E a, ∀ c : Fin n × Fin r,
        coefficients (r := r) E u a z (fun _ => c.1) c.2 = e z c) →
      weightedNormSq (r := r) E g.form h μ φ u ≤
        ENNReal.ofReal (C * ∑ c, ∫ z, ‖e z c‖ ^ 2 ∂lebesgueC n) := by
  obtain ⟨C, hC, hbound⟩ := compact_one_coefficient_norm_upper_bound E g h hh φ hφ a K hK hKO
  refine ⟨(2 : ℝ) ^ n * C, mul_nonneg (pow_nonneg (by norm_num) _) hC, ?_⟩
  intro u hu hz e he hse hcoeff
  apply weightedNormSq_one_le_model_integral E g μ hμ h hh φ hφ a u hu hz e he C hC
  intro z hzo
  by_cases hzK : z ∈ K
  · simpa only [hcoeff z hzo] using hbound u z hzK
  · have hez (c : Fin n × Fin r) : e z c = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w => e w c) (fun hs => hzK (hse c hs))
    have hzero (c : Fin n × Fin r) : coefficients (r := r) E u a z (fun _ => c.1) c.2 = 0 :=
      (hcoeff z hzo c).trans (hez c)
    simp only [chartOneCoefficientNormSq, dotProduct, Matrix.mulVec, Pi.star_apply,
      hzero, hez, star_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

/-- Coefficient convergence on a fixed chart compact gives convergence in the
actual weighted bundle Hilbert space. -/
theorem weightedOneSection_tendsto_of_compact_chart_errors
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (U : ℕ → WeightedOneSection E g μ hμ h hh φ hφ)
    (V : WeightedOneSection E g μ hμ h hh φ hφ)
    (hz : ∀ j x, x ∉ bundleChartSource (r := r) E a → (U j - V).1 x = (0 : NQForm E 1) x)
    (e : ℕ → ComplexVector n → (Fin n × Fin r) → ℂ)
    (he : ∀ j c, MemLp (fun z => e j z c) 2 (lebesgueC n))
    (hse : ∀ j c, tsupport (fun z => e j z c) ⊆ K)
    (hcoeff : ∀ j z, z ∈ localDomain (r := r) E a → ∀ c : Fin n × Fin r,
      coefficients (r := r) E (U j - V).1 a z (fun _ => c.1) c.2 = e j z c)
    (ht : ∀ c, Tendsto (fun j => ∫ z, ‖e j z c‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) :
    Tendsto (fun j => realizeWeightedOneSection E g μ hμ h hh φ hφ (U j))
      atTop (𝓝 (realizeWeightedOneSection E g μ hμ h hh φ hφ V)) := by
  obtain ⟨C, hC, hbound⟩ := weightedNormSq_one_le_compact_model_errors E g μ hμ h hh φ hφ a K hK hKO
  have hsq (j : ℕ) : ‖realizeWeightedOneSection E g μ hμ h hh φ hφ (U j) -
      realizeWeightedOneSection E g μ hμ h hh φ hφ V‖ ^ 2 ≤
        C * ∑ c, ∫ z, ‖e j z c‖ ^ 2 ∂lebesgueC n := by
    rw [← realizeWeightedOneSection_sub E g μ hμ h hh φ hφ, realizeWeightedOneSection_norm_sq]
    have heq := hbound (U j - V).1 (U j - V).2.1 (hz j) (e j) (he j) (hse j) (hcoeff j)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top heq
    rw [ENNReal.toReal_ofReal (mul_nonneg hC (Finset.sum_nonneg fun c _ => integral_nonneg fun z => sq_nonneg _))] at hr
    exact hr
  have hpow : Tendsto (fun j => ‖realizeWeightedOneSection E g μ hμ h hh φ hφ (U j) -
      realizeWeightedOneSection E g μ hμ h hh φ hφ V‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun j => sq_nonneg _) hsq (by
      simpa only [Finset.sum_const_zero, mul_zero] using
        (tendsto_finsetSum Finset.univ (fun c _ => ht c)).const_mul C)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hpow
  simp only [Real.sqrt_zero] at hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hn using 1
  funext j
  exact (Real.sqrt_sq (norm_nonneg _)).symm

end Yau.LeafProofs.L14Aux
