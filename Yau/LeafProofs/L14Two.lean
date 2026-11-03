import Yau.LeafProofs.L14

/-! The actual degree-two norm and the compact chart Dolbeault energy. -/

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix Kronecker
open MeasureTheory Bundle Filter

namespace Yau.LeafProofs.L14Aux
open BundleDbar

def twoCoefficientNormSq {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (F : Fin r → Fin n → Fin n → ℂ) : ℝ :=
  ((1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
    H α β * G⁻¹ i k * G⁻¹ j l * star (F α i j) * F β k l).re

theorem twoCoefficient_contraction_eq_kronecker {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (F : Fin r → Fin n → Fin n → ℂ) :
    (∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
      H α β * G⁻¹ i k * G⁻¹ j l * star (F α i j) * F β k l) =
      star (fun p : (Fin r × Fin n) × Fin n => F p.1.1 p.1.2 p.2) ⬝ᵥ
        ((H ⊗ₖ G⁻¹) ⊗ₖ G⁻¹) *ᵥ (fun p : (Fin r × Fin n) × Fin n => F p.1.1 p.1.2 p.2) := by
  classical
  let e : (Fin r × Fin r × Fin n × Fin n × Fin n × Fin n) ≃
      (Fin r × Fin n × Fin n × Fin r × Fin n × Fin n) :=
    { toFun := fun ⟨α, β, i, j, k, l⟩ => (α, i, j, β, k, l)
      invFun := fun ⟨α, i, j, β, k, l⟩ => (α, β, i, j, k, l)
      left_inv := by rintro ⟨α, β, i, j, k, l⟩; rfl
      right_inv := by rintro ⟨α, i, j, β, k, l⟩; rfl }
  have hperm (f : Fin r → Fin r → Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l, f α β i j k l) =
        ∑ α, ∑ i, ∑ j, ∑ β, ∑ k, ∑ l, f α β i j k l := by
    simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
      (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (fun p => f p.1 p.2.2.2.1 p.2.1 p.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (by rintro ⟨α, β, i, j, k, l⟩; rfl)
  simp only [dotProduct, Matrix.mulVec, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [hperm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem twoCoefficientNormSq_nonneg {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.PosDef) (hH : H.PosDef) (F : Fin r → Fin n → Fin n → ℂ) :
    0 ≤ twoCoefficientNormSq G H F := by
  unfold twoCoefficientNormSq
  rw [twoCoefficient_contraction_eq_kronecker]
  have hpos := (Complex.nonneg_iff.mp
    (((hH.kronecker hG.inv).kronecker hG.inv).posSemidef.dotProduct_mulVec_nonneg
      (fun p : (Fin r × Fin n) × Fin n => F p.1.1 p.1.2 p.2))).1
  have hhalf (c : ℂ) : ((1 / 2 : ℂ) * c).re = (1 / 2 : ℝ) * c.re := by
    norm_num [Complex.mul_re]
  rw [hhalf]
  exact mul_nonneg (by norm_num) hpos

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem formNormSq_two_nonneg (g : HermitianField M) (h : Metric E)
    (u : NQForm E 2) (x : M.Carrier) :
    0 ≤ BundleDbar.formNormSq (r := r) E g h u x := by
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have he := formNormSq_two_chart_factor E g h u x (chartPt x x) hz
  rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)] at he
  rw [he]
  exact mul_nonneg (inv_nonneg.mpr (L18Aux.hMat_det_re_pos g x hz.1).le)
    (twoCoefficientNormSq_nonneg _ _ (hMat_posDef g x _ hz.1)
      (metricMatrix_posDef E h x _ hz) (fun α i j => coefficients (r := r) E u x (chartPt x x) ![i,j] α))

theorem formNormSq_two_continuous (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (u : NQForm E 2)
    (hu : SmoothForm (r := r) E u) :
    Continuous (BundleDbar.formNormSq (r := r) E g.form h u) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let O := localDomain (r := r) E x
  have hself : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hz : chartPt x x ∈ O := by
    refine ⟨(extChartAt (ComplexModel n) x).map_source hself.1, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hself.2
  have hd : ContinuousOn (fun z => ((hMat g.form x z).det.re)⁻¹) O :=
    ((Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g x)).continuousOn).inv₀
        (fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form x hz))).mono Set.inter_subset_left
  let Q := fun z => twoCoefficientNormSq (hMat g.form x z)
    (BundleDbar.metricMatrix (r := r) E h x z)
      (fun α i j => coefficients (r := r) E u x z ![i,j] α)
  have hQ : ContinuousOn Q O := by
    unfold Q twoCoefficientNormSq
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_const.mul
    apply continuousOn_finset_sum
    intro α _
    apply continuousOn_finset_sum
    intro β _
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    apply continuousOn_finset_sum
    intro k _
    apply continuousOn_finset_sum
    intro l _
    exact (((((hh x α β).continuousOn.mul
      ((L18Aux.hMat_inverse_contDiffOn g x i k).continuousOn.mono Set.inter_subset_left)).mul
      ((L18Aux.hMat_inverse_contDiffOn g x j l).continuousOn.mono Set.inter_subset_left)).mul
      (continuous_star.comp_continuousOn (hu x ![i,j] α).continuousOn)).mul
      (hu x ![k,l] β).continuousOn)
  let J := fun z => ((hMat g.form x z).det.re)⁻¹ * Q z
  have hJ : ContinuousAt J (chartPt x x) :=
    (hd.mul hQ).continuousAt ((localDomain_isOpen E x).mem_nhds hz)
  have hchart : ContinuousAt (chartPt x) x :=
    (continuousOn_extChartAt (I := ComplexModel n) x).continuousAt
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hself.1)
  have heq : BundleDbar.formNormSq (r := r) E g.form h u =ᶠ[𝓝 x]
      (fun y => J (chartPt x y)) := by
    filter_upwards [(bundleChartSource_isOpen (r := r) E x).mem_nhds hself] with y hy
    have hzy : chartPt x y ∈ O := by
      refine ⟨(extChartAt (ComplexModel n) x).map_source hy.1, ?_⟩
      change chartInv x (chartPt x y) ∈ (localTriv (r := r) E x).baseSet
      rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)]
      exact hy.2
    have hf := formNormSq_two_chart_factor E g.form h u x (chartPt x y) hzy
    rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)] at hf
    exact hf
  exact (hJ.comp hchart).congr_of_eventuallyEq heq

theorem smooth_compact_weightedL2_two (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 2)
    (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 2) x})) :
    WeightedL2 (r := r) E g.form h μ φ u := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  let F := fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)
  have hF : Continuous F := (formNormSq_two_continuous E g h hh u hu).mul
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg)
  have hs : Function.support F ⊆ {x | u x ≠ (0 : NQForm E 2) x} := by
    intro x hx hz
    apply hx
    change BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) = 0
    rw [formNormSq_congr_at E g.form h u (0 : NQForm E 2) x hz, formNormSq_zero, zero_mul]
  have hcF : HasCompactSupport F := hc.of_isClosed_subset isClosed_closure (closure_mono hs)
  have hi : Integrable F μ := hF.integrable_of_hasCompactSupport hcF
  exact ⟨smoothForm_locallyL2 E u hu,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
      mul_nonneg (formNormSq_two_nonneg E g.form h u x) (Real.exp_pos _).le)).mp hi.2⟩

theorem twoFormPushforward_weightedL2 (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    WeightedL2 (r := r) E g.form h μ φ (twoFormPushforward (r := r) E a F) := by
  apply smooth_compact_weightedL2_two E g μ hμ h hh φ hφ _
    (twoFormPushforward_smooth E hE a F hskew hF hc hs)
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (twoFormPushforward_support E a F hc hs)

theorem weighted_two_chart_integral (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 2) (hu : SmoothForm (r := r) E u) (a : M.Carrier) :
    (∫⁻ x in bundleChartSource (r := r) E a,
      ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ) =
      ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (twoCoefficientNormSq (hMat g.form a z)
          (BundleDbar.metricMatrix (r := r) E h a z)
          (fun α i j => coefficients (r := r) E u a z ![i,j] α) * Real.exp (-φ (chartInv a z)))
          ∂lebesgueC n := by
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEMeasurable (fun x => ENNReal.ofReal
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((formNormSq_two_continuous E g h hh u hu).measurable.aemeasurable.mul hw.aemeasurable)
  rw [lintegral_bundleChart_volume (r := r) E g μ hμ a _ hm,
    ← lintegral_const_mul' (ENNReal.ofReal ((2 : ℝ) ^ n)) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), realMetricFn_sqrt_det g.form a z hz.1,
    formNormSq_two_chart_factor E g.form h u a z hz,
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  congr 1
  change ((2 : ℝ) ^ n * (hMat g.form a z).det.re) *
      (((hMat g.form a z).det.re)⁻¹ * twoCoefficientNormSq (hMat g.form a z)
        (BundleDbar.metricMatrix (r := r) E h a z)
          (fun α i j => coefficients (r := r) E u a z ![i,j] α) * Real.exp (-φ (chartInv a z))) = _
  field_simp [ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz.1)]

theorem twoCoefficientNormSq_smul_metric {d s : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin s) (Fin s) ℂ)
    (F : Fin s → Fin d → Fin d → ℂ) (c : ℝ) :
    twoCoefficientNormSq G ((c : ℂ) • H) F = c * twoCoefficientNormSq G H F := by
  unfold twoCoefficientNormSq
  have he : (1 / 2 : ℂ) * (∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
      ((c : ℂ) • H) α β * G⁻¹ i k * G⁻¹ j l * star (F α i j) * F β k l) =
      (c : ℂ) * ((1 / 2 : ℂ) * ∑ α, ∑ β, ∑ i, ∑ j, ∑ k, ∑ l,
        H α β * G⁻¹ i k * G⁻¹ j l * star (F α i j) * F β k l) := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem weightedNormSq_modelOneDbar (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (hE : Holomorphic (r := r) E) (a : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    weightedNormSq (r := r) E g.form h μ φ
      (twoFormPushforward (r := r) E a (modelOneDbar F)) =
      ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (localCurlEnergy (hMat g.form a z)
          (weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ) z) F z)
          ∂lebesgueC n := by
  let u := twoFormPushforward (r := r) E a (modelOneDbar F)
  have hu : SmoothForm (r := r) E u := twoFormPushforward_modelOneDbar_smooth E hE a F hF hc hs
  have hcD : HasCompactSupport (modelOneDbar F) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset F)
  have hsD : tsupport (modelOneDbar F) ⊆ localDomain (r := r) E a :=
    (tsupport_modelOneDbar_subset F).trans hs
  have hsU := twoFormPushforward_support_in_source E a (modelOneDbar F) hcD hsD
  calc
    _ = ∫⁻ x in bundleChartSource (r := r) E a,
        ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ∂μ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra hnsource
      have hz : u x = (0 : NQForm E 2) x := by
        by_contra hn
        exact hnsource (hsU (subset_closure hn))
      apply hx
      change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) = 0
      rw [formNormSq_congr_at E g.form h u (0 : NQForm E 2) x hz, formNormSq_zero,
        zero_mul, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal (twoCoefficientNormSq (hMat g.form a z)
          (BundleDbar.metricMatrix (r := r) E h a z)
          (fun α i j => coefficients (r := r) E u a z ![i,j] α) * Real.exp (-φ (chartInv a z)))
          ∂lebesgueC n := weighted_two_chart_integral E g μ hμ h hh φ hφ u hu a
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
      congr 1
      dsimp only [u]
      simp_rw [twoFormPushforward_coefficients E a _ (modelOneDbar_skew F) z hz]
      change twoCoefficientNormSq (hMat g.form a z) (BundleDbar.metricMatrix (r := r) E h a z)
        (fun α i j => localCurlMatrix F z α i j) * Real.exp (-φ (chartInv a z)) =
          twoCoefficientNormSq (hMat g.form a z)
            ((Real.exp (-inChart a φ z) : ℂ) • BundleDbar.metricMatrix (r := r) E h a z)
              (fun α i j => localCurlMatrix F z α i j)
      rw [twoCoefficientNormSq_smul_metric]
      exact mul_comm _ _

end Yau.LeafProofs.L14Aux
