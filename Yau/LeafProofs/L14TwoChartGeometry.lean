import Yau.LeafProofs.L14ModelL2

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder Kronecker ENNReal
open MeasureTheory Bundle Filter Module
open Yau
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

abbrev TwoCoefficientIndex (n r : ℕ) := (Fin r × Fin n) × Fin n

def chartTwoMetricMatrix (g : HermitianField M) (h : Metric E) (a : M.Carrier) (z : ComplexVector n) :
    Matrix (TwoCoefficientIndex n r) (TwoCoefficientIndex n r) ℂ :=
  (BundleDbar.metricMatrix (r := r) E h a z ⊗ₖ (hMat g a z)⁻¹) ⊗ₖ (hMat g a z)⁻¹

def chartTwoCoefficientNormSq (g : HermitianField M) (h : Metric E) (u : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) : ℝ :=
  (1 / 2 : ℝ) * (star (fun p : TwoCoefficientIndex n r => coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1) ⬝ᵥ
    chartTwoMetricMatrix (r := r) E g h a z *ᵥ
      (fun p : TwoCoefficientIndex n r => coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1)).re

theorem chartTwoCoefficientNormSq_eq (g : HermitianField M) (h : Metric E) (u : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) :
    chartTwoCoefficientNormSq (r := r) E g h u a z = twoCoefficientNormSq (hMat g a z)
      (BundleDbar.metricMatrix (r := r) E h a z) (fun α i j => coefficients (r := r) E u a z ![i,j] α) := by
  unfold chartTwoCoefficientNormSq twoCoefficientNormSq
  rw [twoCoefficient_contraction_eq_kronecker]
  norm_num [chartTwoMetricMatrix, Complex.mul_re]

theorem chartTwoMetricMatrix_posDef (g : HermitianField M) (h : Metric E)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    (chartTwoMetricMatrix (r := r) E g h a z).PosDef :=
  ((metricMatrix_posDef E h a z hz).kronecker (hMat_posDef g a z hz.1).inv).kronecker (hMat_posDef g a z hz.1).inv

theorem chartTwoMetricMatrix_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (a : M.Carrier) (p q : TwoCoefficientIndex n r) :
    ContDiffOn ℝ ∞ (fun z => chartTwoMetricMatrix (r := r) E g.form h a z p q) (localDomain (r := r) E a) := by
  change ContDiffOn ℝ ∞ (fun z => BundleDbar.metricMatrix (r := r) E h a z p.1.1 q.1.1 *
    (hMat g.form a z)⁻¹ p.1.2 q.1.2 * (hMat g.form a z)⁻¹ p.2 q.2) _
  exact ((hh a p.1.1 q.1.1).mul
    ((L18Aux.hMat_inverse_contDiffOn g a p.1.2 q.1.2).mono Set.inter_subset_left)).mul
      ((L18Aux.hMat_inverse_contDiffOn g a p.2 q.2).mono Set.inter_subset_left)

theorem formNormSq_two_chart_factor_matrix (g : HermitianField M) (h : Metric E) (u : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    BundleDbar.formNormSq (r := r) E g h u (chartInv a z) =
      ((hMat g a z).det.re)⁻¹ * chartTwoCoefficientNormSq (r := r) E g h u a z := by
  rw [chartTwoCoefficientNormSq_eq]
  exact formNormSq_two_chart_factor E g h u a z hz

theorem two_coefficient_le_inverse_diagonal (g : HermitianField M) (h : Metric E) (u : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (p : TwoCoefficientIndex n r) :
    ‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2 ≤
      (2 * ((chartTwoMetricMatrix (r := r) E g h a z)⁻¹ p p).re) * chartTwoCoefficientNormSq (r := r) E g h u a z := by
  have he := matrix_coordinate_le_inverse_diagonal _ (chartTwoMetricMatrix_posDef (r := r) E g h a z hz)
    (fun p : TwoCoefficientIndex n r => coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1) p
  dsimp only [chartTwoCoefficientNormSq]
  nlinarith

theorem chartTwoCoefficientNormSq_aemeasurable (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (u : NQForm E 2)
    (hu : LocallyL2 (r := r) E u) (a : M.Carrier) :
    AEMeasurable (chartTwoCoefficientNormSq (r := r) E g.form h u a)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  have hA (p q : TwoCoefficientIndex n r) :
      AEMeasurable (fun z => chartTwoMetricMatrix (r := r) E g.form h a z p q)
        ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    ((chartTwoMetricMatrix_contDiffOn E g h hh a p q).continuousOn.aestronglyMeasurable
      (localDomain_isOpen E a).measurableSet).aemeasurable
  have hU (p : TwoCoefficientIndex n r) : AEMeasurable
      (fun z => coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := (hu a ![p.1.2,p.2] p.1.1).1.aemeasurable
  unfold chartTwoCoefficientNormSq
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply AEMeasurable.const_mul
  apply Complex.measurable_re.comp_aemeasurable
  apply Finset.univ.aemeasurable_fun_sum
  intro p _
  apply Finset.univ.aemeasurable_fun_sum
  intro q _
  exact (continuous_star.measurable.comp_aemeasurable (hU p)).mul ((hA p q).mul (hU q))

theorem formNormSq_two_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u : NQForm E 2) (hu : LocallyL2 (r := r) E u) :
    AEMeasurable (BundleDbar.formNormSq (r := r) E g.form h u) μ := by
  apply aemeasurable_of_bundleCharts (r := r) E g.form μ hμ
  intro a
  have hdc : ContinuousOn (fun z => (hMat g.form a z).det.re) (localDomain (r := r) E a) :=
    (Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn).mono Set.inter_subset_left
  have hd : AEMeasurable (fun z => ((hMat g.form a z).det.re)⁻¹)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    (hdc.aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable.inv
  apply (hd.mul (chartTwoCoefficientNormSq_aemeasurable E g h hh u hu a)).congr
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  exact (formNormSq_two_chart_factor_matrix E g.form h u a z hz).symm

theorem weighted_two_chart_integral_rough (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 2) (hu : LocallyL2 (r := r) E u) (a : M.Carrier) :
    (∫⁻ x in bundleChartSource (r := r) E a, ENNReal.ofReal
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ) =
      ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEMeasurable (fun x => ENNReal.ofReal
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((formNormSq_two_aemeasurable E g μ hμ h hh u hu).mul hw.aemeasurable)
  rw [lintegral_bundleChart_volume (r := r) E g μ hμ a _ hm,
    ← lintegral_const_mul' (ENNReal.ofReal ((2 : ℝ) ^ n)) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), realMetricFn_sqrt_det g.form a z hz.1,
    formNormSq_two_chart_factor_matrix E g.form h u a z hz,
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  congr 1
  change ((2 : ℝ) ^ n * (hMat g.form a z).det.re) *
    (((hMat g.form a z).det.re)⁻¹ * chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) = _
  field_simp [ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz.1)]

theorem chartTwoCoefficientNormSq_nonneg (g : HermitianField M) (h : Metric E) (u : NQForm E 2)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    0 ≤ chartTwoCoefficientNormSq (r := r) E g h u a z := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact (Complex.nonneg_iff.mp ((chartTwoMetricMatrix_posDef E g h a z hz).posSemidef.dotProduct_mulVec_nonneg _)).1

theorem compact_two_coefficient_weight_bound (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (p : TwoCoefficientIndex n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 2) z, z ∈ K →
      ‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2 ≤
        C * (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) := by
  have hdet : ∀ z ∈ localDomain (r := r) E a,
      (chartTwoMetricMatrix (r := r) E g.form h a z).det ≠ 0 := fun z hz =>
    ((chartTwoMetricMatrix_posDef (r := r) E g.form h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  have hi : ContinuousOn (fun z => (2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re))
      (localDomain (r := r) E a) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_inv (chartTwoMetricMatrix_contDiffOn (r := r) E g h hh a) hdet p p).continuousOn)
  have he : ContinuousOn (fun z => Real.exp (inChart a φ z)) (localDomain (r := r) E a) :=
    Real.continuous_exp.comp_continuousOn ((hφ a).continuousOn.mono Set.inter_subset_left)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((hi.mul he).mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro u z hz
  have hzdom := hsub hz
  have hC : (2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re) * Real.exp (inChart a φ z) ≤ max B 0 := by
    apply le_trans (le_abs_self _)
    have hb : ‖(2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re) * Real.exp (inChart a φ z)‖ ≤ B := hB z hz
    exact (show |(2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re) * Real.exp (inChart a φ z)| ≤ B from
      by simpa only [Real.norm_eq_abs] using hb).trans (le_max_left _ _)
  have hq : 0 ≤ chartTwoCoefficientNormSq (r := r) E g.form h u a z := chartTwoCoefficientNormSq_nonneg (r := r) E g.form h u a z hzdom
  have hw : Real.exp (inChart a φ z) * Real.exp (-φ (chartInv a z)) = 1 := by
    change Real.exp (φ (chartInv a z)) * Real.exp (-φ (chartInv a z)) = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ ≤ (2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re) * chartTwoCoefficientNormSq (r := r) E g.form h u a z :=
      two_coefficient_le_inverse_diagonal (r := r) E g.form h u a z hzdom p
    _ = ((2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re) * Real.exp (inChart a φ z)) *
        (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) := by
      calc
        _ = ((2 * ((chartTwoMetricMatrix (r := r) E g.form h a z)⁻¹ p p).re) * chartTwoCoefficientNormSq (r := r) E g.form h u a z) *
            (Real.exp (inChart a φ z) * Real.exp (-φ (chartInv a z))) := by rw [hw, mul_one]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (mul_nonneg hq (Real.exp_pos _).le)

theorem compact_two_coefficient_norm_upper_bound (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 2) z, z ∈ K →
      chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z)) ≤
        C * ∑ p : TwoCoefficientIndex n r, ‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2 := by
  classical
  let B := fun z => ((1 / 2 : ℝ) * ∑ p, ∑ q, ‖chartTwoMetricMatrix (r := r) E g.form h a z p q‖) *
    Real.exp (-φ (chartInv a z))
  have hB : ContinuousOn B (localDomain (r := r) E a) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.const_mul
      apply continuousOn_finsetSum
      intro p _
      apply continuousOn_finsetSum
      intro q _
      exact ((chartTwoMetricMatrix_contDiffOn E g h hh a p q).continuousOn).norm
    · exact Real.continuous_exp.comp_continuousOn (((hφ a).continuousOn.mono Set.inter_subset_left).neg)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hB.mono hKO)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u z hz
  have hS : 0 ≤ ∑ p : TwoCoefficientIndex n r, ‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : B z ≤ max C 0 := (le_abs_self _).trans
    ((show |B z| ≤ C from hC z hz).trans (le_max_left _ _))
  have he := matrix_quadratic_re_le_coefficient_sq (chartTwoMetricMatrix (r := r) E g.form h a z)
    (fun p : TwoCoefficientIndex n r => coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1)
  calc
    _ ≤ ((1 / 2 : ℝ) * ((∑ p, ∑ q, ‖chartTwoMetricMatrix (r := r) E g.form h a z p q‖) *
        ∑ p : TwoCoefficientIndex n r, ‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2)) *
        Real.exp (-φ (chartInv a z)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (Real.exp_pos _).le
    _ = B z * ∑ p : TwoCoefficientIndex n r, ‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2 := by dsimp only [B]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hS

theorem compact_two_coefficient_integral_bound (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hsub : K ⊆ localDomain (r := r) E a) (p : TwoCoefficientIndex n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : NQForm E 2, LocallyL2 (r := r) E u →
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z ![p.1.2,p.2] p.1.1‖ ^ 2) ∂lebesgueC n) ≤
        ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ φ u := by
  obtain ⟨C, hC, hbound⟩ := compact_two_coefficient_weight_bound (r := r) E g h hh φ hφ a K hK hsub p
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hTwo : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
    have ht : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht
  have hnormal : (∫⁻ z in localDomain (r := r) E a,
      ENNReal.ofReal (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n) ≤
        weightedNormSq (r := r) E g.form h μ φ u := by
    calc
      _ = 1 * ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by rw [one_mul]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (chartTwoCoefficientNormSq (r := r) E g.form h u a z * Real.exp (-φ (chartInv a z))) ∂lebesgueC n :=
        mul_le_mul_left hTwo _
      _ = _ := (weighted_two_chart_integral_rough E g μ hμ h hh φ hφ u hu a).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  calc
    _ ≤ ∫⁻ z in K, ENNReal.ofReal (C * (chartTwoCoefficientNormSq (r := r) E g.form h u a z *
        Real.exp (-φ (chartInv a z)))) ∂lebesgueC n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact ENNReal.ofReal_le_ofReal (hbound u z hz)
    _ = ENNReal.ofReal C * ∫⁻ z in K, ENNReal.ofReal (chartTwoCoefficientNormSq (r := r) E g.form h u a z *
        Real.exp (-φ (chartInv a z))) ∂lebesgueC n := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right ((lintegral_mono_set hsub).trans hnormal) _

theorem weightedTwoNorm_integrable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 2)
    (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) μ := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm := (formNormSq_two_aemeasurable E g μ hμ h hh u hu.1).mul hw.aemeasurable
  refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun x => mul_nonneg (formNormSq_two_nonneg E g.form h u x) (Real.exp_pos _).le)).mpr hu.2⟩

theorem weightedNormSq_two_eq_ofReal_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 2)
    (hu : WeightedL2 (r := r) E g.form h μ φ u) :
    weightedNormSq (r := r) E g.form h μ φ u = ENNReal.ofReal
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal (weightedTwoNorm_integrable E g μ hμ h hh φ hφ u hu)
    (Eventually.of_forall fun x => mul_nonneg (formNormSq_two_nonneg E g.form h u x) (Real.exp_pos _).le)).symm

end Yau.LeafProofs.L14Aux
