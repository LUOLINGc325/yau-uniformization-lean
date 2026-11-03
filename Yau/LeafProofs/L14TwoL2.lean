import Yau.LeafProofs.L14TwoInner
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

theorem twoFormPairing_inChart_aemeasurable (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (u v : NQForm E 2)
    (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) (a : M.Carrier) :
    AEMeasurable (fun z => twoFormPairing E g.form h u v (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  have hD : AEMeasurable (fun z => ((hMat g.form a z).det.re : ℂ))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    apply Complex.continuous_ofReal.measurable.comp_aemeasurable
    exact (((Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn).mono
        Set.inter_subset_left).aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable
  have hInv (i j : Fin n) : AEMeasurable (fun z => (hMat g.form a z)⁻¹ i j)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    have hc := (L18Aux.hMat_inverse_contDiffOn g a i j).continuousOn.mono
      (show localDomain (r := r) E a ⊆ chartTarget a from Set.inter_subset_left)
    exact (hc.aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable
  have hH (α β : Fin r) : AEMeasurable (fun z => BundleDbar.metricMatrix (r := r) E h a z α β)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    ((hh a α β).continuousOn.aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable
  have hm : AEMeasurable (fun z => (1 / 2 : ℂ) *
      ∑ i, ∑ k, ∑ j, ∑ l, (hMat g.form a z)⁻¹ i k * (hMat g.form a z)⁻¹ j l *
        ((∑ α, ∑ β, star (coefficients (r := r) E u a z ![i,j] α) *
          BundleDbar.metricMatrix (r := r) E h a z α β * coefficients (r := r) E v a z ![k,l] β) /
          ((hMat g.form a z).det.re : ℂ)))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
    apply AEMeasurable.const_mul
    apply Finset.univ.aemeasurable_fun_sum
    intro i _
    apply Finset.univ.aemeasurable_fun_sum
    intro k _
    apply Finset.univ.aemeasurable_fun_sum
    intro j _
    apply Finset.univ.aemeasurable_fun_sum
    intro l _
    apply ((hInv i k).mul (hInv j l)).mul
    apply AEMeasurable.div _ hD
    apply Finset.univ.aemeasurable_fun_sum
    intro α _
    apply Finset.univ.aemeasurable_fun_sum
    intro β _
    exact ((continuous_star.measurable.comp_aemeasurable (hu a ![i,j] α).1.aemeasurable).mul (hH α β)).mul
      (hv a ![k,l] β).1.aemeasurable
  apply hm.congr
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  exact (twoFormPairing_inChart E g.form h u v a z hz).symm

theorem twoFormPairing_aemeasurable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (u v : NQForm E 2) (hu : LocallyL2 (r := r) E u) (hv : LocallyL2 (r := r) E v) :
    AEMeasurable (twoFormPairing E g.form h u v) μ :=
  aemeasurable_complex_of_bundleCharts E g.form μ hμ _
    (twoFormPairing_inChart_aemeasurable E g h hh u v hu hv)

theorem formNormSq_two_add_le (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 2) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (u+v) x ≤
      2 * BundleDbar.formNormSq (r := r) E g h u x + 2 * BundleDbar.formNormSq (r := r) E g h v x := by
  letI : PreInnerProductSpace.Core ℂ (NQForm E 2) := twoFormPointPreInner (r := r) E g h x
  have hp := congrArg Complex.re (InnerProductSpace.Core.inner_add_add_self (𝕜 := ℂ) u v)
  have hm := congrArg Complex.re (InnerProductSpace.Core.inner_sub_sub_self (𝕜 := ℂ) u v)
  change (twoFormPairing E g h (u+v) (u+v) x).re =
    (twoFormPairing E g h u u x + twoFormPairing E g h u v x +
      twoFormPairing E g h v u x + twoFormPairing E g h v v x).re at hp
  change (twoFormPairing E g h (u-v) (u-v) x).re =
    (twoFormPairing E g h u u x - twoFormPairing E g h u v x -
      twoFormPairing E g h v u x + twoFormPairing E g h v v x).re at hm
  simp only [Complex.add_re, Complex.sub_re, twoFormPairing_self_re (r := r) E g h] at hp hm
  nlinarith [formNormSq_two_nonneg (r := r) E g h (u-v) x]

theorem formNormSq_two_smul (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u : NQForm E 2) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (c • u) x = Complex.normSq c * BundleDbar.formNormSq (r := r) E g h u x := by
  rw [← twoFormPairing_self_re (r := r) E g h (c • u) x, twoFormPairing_smul_left, twoFormPairing_smul_right]
  have he : star c * (c * twoFormPairing E g h u u x) = (Complex.normSq c : ℂ) * twoFormPairing E g h u u x := by
    rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    twoFormPairing_self_re (r := r) E g h]

theorem weightedNormSq_two_smul (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (c : ℂ) (u : NQForm E 2) :
    weightedNormSq (r := r) E g h μ φ (c • u) =
      ENNReal.ofReal (Complex.normSq c) * weightedNormSq (r := r) E g h μ φ u := by
  unfold weightedNormSq
  simp_rw [formNormSq_two_smul, mul_assoc, ENNReal.ofReal_mul (Complex.normSq_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedL2_two_zero (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) :
    WeightedL2 (r := r) E g h μ φ (0 : NQForm E 2) := by
  refine ⟨locallyL2_zero E 2, ?_⟩
  simp [weightedNormSq, BundleDbar.formNormSq, coefficients_zero]

theorem weightedL2_two_smul (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (c : ℂ) (u : NQForm E 2)
    (hu : WeightedL2 (r := r) E g h μ φ u) : WeightedL2 (r := r) E g h μ φ (c • u) := by
  refine ⟨locallyL2_smul E c u hu.1, ?_⟩
  rw [weightedNormSq_two_smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2


theorem weightedL2_two_add (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u v : NQForm E 2) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (hv : WeightedL2 (r := r) E g.form h μ φ v) :
    WeightedL2 (r := r) E g.form h μ φ (u + v) := by
  have hlocal := locallyL2_add E u v hu.1 hv.1
  have hw : Measurable (fun x => Real.exp (-φ x)) :=
    (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  have hm : AEStronglyMeasurable (fun x => BundleDbar.formNormSq (r := r) E g.form h (u + v) x *
      Real.exp (-φ x)) μ :=
    ((L14Aux.formNormSq_two_aemeasurable E g μ hμ h hh (u + v) hlocal).mul hw.aemeasurable).aestronglyMeasurable
  have hdom := ((L14Aux.weightedTwoNorm_integrable E g μ hμ h hh φ hφ u hu).const_mul 2).add
    ((L14Aux.weightedTwoNorm_integrable E g μ hμ h hh φ hφ v hv).const_mul 2)
  have hn : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (L14Aux.formNormSq_two_nonneg (r := r) E g.form h (u + v) x)
      (Real.exp_pos _).le
  have hi : Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x)) μ := by
    apply hdom.mono' hm
    filter_upwards [hn] with x hnx
    change ‖BundleDbar.formNormSq (r := r) E g.form h (u + v) x * Real.exp (-φ x)‖ ≤
      2 * (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) +
        2 * (BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x))
    rw [Real.norm_of_nonneg hnx]
    have ht := mul_le_mul_of_nonneg_right (formNormSq_two_add_le (r := r) E g.form h u v x)
      (Real.exp_pos (-φ x)).le
    nlinarith
  exact ⟨hlocal, (hasFiniteIntegral_iff_ofReal hn).mp hi.2⟩

def weightedTwoFormSubmodule (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) :
    Submodule ℂ (NQForm E 2) where
  carrier := {u | WeightedL2 (r := r) E g.form h μ φ u}
  zero_mem' := weightedL2_two_zero E g.form h μ φ
  add_mem' := fun hu hv => weightedL2_two_add E g μ hμ h hh φ hφ _ _ hu hv
  smul_mem' := fun c u hu => weightedL2_two_smul E g.form h μ φ c u hu

def weightedTwoPairing (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u v : NQForm E 2) (x : M.Carrier) : ℂ :=
  twoFormPairing E g h u v x * (Real.exp (-φ x) : ℂ)

theorem weightedTwoPairing_self_re (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 2) (x : M.Carrier) :
    (weightedTwoPairing E g h φ u u x).re =
      BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) := by
  simp only [weightedTwoPairing, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [twoFormPairing_self_re (r := r)]

theorem weightedTwoPairing_integrable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u v : NQForm E 2) (hu : WeightedL2 (r := r) E g.form h μ φ u)
    (hv : WeightedL2 (r := r) E g.form h μ φ v) :
    Integrable (weightedTwoPairing E g.form h φ u v) μ := by
  have hw : AEMeasurable (fun x => (Real.exp (-φ x) : ℂ)) μ :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable
      (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable.aemeasurable
  have hm : AEStronglyMeasurable (weightedTwoPairing E g.form h φ u v) μ :=
    ((twoFormPairing_aemeasurable E g μ hμ h hh u v hu.1 hv.1).mul hw).aestronglyMeasurable
  have ha : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_two_nonneg (r := r) E g.form h u x) (Real.exp_pos _).le
  have hb : ∀ᵐ x ∂μ, 0 ≤ BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (formNormSq_two_nonneg (r := r) E g.form h v x) (Real.exp_pos _).le
  have hbound : ∀ᵐ x ∂μ, Complex.normSq (weightedTwoPairing E g.form h φ u v x) ≤
      (BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) *
        (BundleDbar.formNormSq (r := r) E g.form h v x * Real.exp (-φ x)) := by
    apply Filter.Eventually.of_forall
    intro x
    unfold weightedTwoPairing
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    calc
      _ ≤ (BundleDbar.formNormSq (r := r) E g.form h u x * BundleDbar.formNormSq (r := r) E g.form h v x) *
          (Real.exp (-φ x) * Real.exp (-φ x)) :=
        mul_le_mul_of_nonneg_right (twoFormPairing_cauchySchwarz (r := r) E g.form h u v x)
          (mul_self_nonneg (Real.exp (-φ x)))
      _ = _ := by ring
  exact integrable_of_normSq_le_mul μ _ _ _ hm
    (weightedTwoNorm_integrable E g μ hμ h hh φ hφ u hu)
    (weightedTwoNorm_integrable E g μ hμ h hh φ hφ v hv) ha hb hbound

def weightedTwoInner (g : HermitianField M) (μ : Measure M.Carrier) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v : NQForm E 2) : ℂ :=
  ∫ x, weightedTwoPairing E g h φ u v x ∂μ

@[instance_reducible]
def weightedTwoFormPreInner (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) :
    PreInnerProductSpace.Core ℂ (weightedTwoFormSubmodule (r := r) E g μ hμ h hh φ hφ) where
  inner u v := weightedTwoInner E g.form μ h φ u.1 v.1
  conj_inner_symm u v := by
    change star (∫ x, weightedTwoPairing E g.form h φ v.1 u.1 x ∂μ) =
      ∫ x, weightedTwoPairing E g.form h φ u.1 v.1 x ∂μ
    calc
      _ = ∫ x, star (weightedTwoPairing E g.form h φ v.1 u.1 x) ∂μ := (integral_conj (f := weightedTwoPairing E g.form h φ v.1 u.1)).symm
      _ = _ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change star (twoFormPairing E g.form h v.1 u.1 x * (Real.exp (-φ x) : ℂ)) =
          twoFormPairing E g.form h u.1 v.1 x * (Real.exp (-φ x) : ℂ)
        rw [star_mul, twoFormPairing_conj_symm,
          show star (Real.exp (-φ x) : ℂ) = (Real.exp (-φ x) : ℂ) from by
            simp only [Complex.star_def, Complex.conj_ofReal]]
        ring
  re_inner_nonneg u := by
    change 0 ≤ (∫ x, weightedTwoPairing E g.form h φ u.1 u.1 x ∂μ).re
    have hp := weightedTwoPairing_integrable E g μ hμ h hh φ hφ u.1 u.1 u.2 u.2
    have hr : (∫ x, (weightedTwoPairing E g.form h φ u.1 u.1 x).re ∂μ) =
        (∫ x, weightedTwoPairing E g.form h φ u.1 u.1 x ∂μ).re := by
      simpa only [RCLike.re_eq_complex_re] using integral_re (𝕜 := ℂ) hp
    rw [← hr]
    apply integral_nonneg
    intro x
    change 0 ≤ (weightedTwoPairing E g.form h φ u.1 u.1 x).re
    rw [weightedTwoPairing_self_re (r := r)]
    exact mul_nonneg (formNormSq_two_nonneg E g.form h u.1 x) (Real.exp_pos _).le
  add_left u v w := by
    change weightedTwoInner E g.form μ h φ (u.1 + v.1) w.1 =
      weightedTwoInner E g.form μ h φ u.1 w.1 + weightedTwoInner E g.form μ h φ v.1 w.1
    unfold weightedTwoInner
    calc
      _ = ∫ x, weightedTwoPairing E g.form h φ u.1 w.1 x + weightedTwoPairing E g.form h φ v.1 w.1 x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        unfold weightedTwoPairing
        rw [twoFormPairing_add_left, add_mul]
      _ = _ := integral_add (weightedTwoPairing_integrable E g μ hμ h hh φ hφ u.1 w.1 u.2 w.2)
        (weightedTwoPairing_integrable E g μ hμ h hh φ hφ v.1 w.1 v.2 w.2)
  smul_left u v c := by
    change weightedTwoInner E g.form μ h φ (c • u.1) v.1 = star c * weightedTwoInner E g.form μ h φ u.1 v.1
    unfold weightedTwoInner
    calc
      _ = ∫ x, star c * weightedTwoPairing E g.form h φ u.1 v.1 x ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        unfold weightedTwoPairing
        rw [twoFormPairing_smul_left]
        ring
      _ = _ := integral_const_mul _ _


def WeightedTwoSection (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) : Type :=
  weightedTwoFormSubmodule (r := r) E g μ hμ h hh φ hφ

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

instance weightedTwoSectionAddCommGroup : AddCommGroup (WeightedTwoSection E g μ hμ h hh φ hφ) :=
  (weightedTwoFormSubmodule (r := r) E g μ hμ h hh φ hφ).addCommGroup

instance weightedTwoSectionModule : Module ℂ (WeightedTwoSection E g μ hμ h hh φ hφ) :=
  (weightedTwoFormSubmodule (r := r) E g μ hμ h hh φ hφ).module

instance weightedTwoSectionSeminormedAddCommGroup :
    SeminormedAddCommGroup (WeightedTwoSection E g μ hμ h hh φ hφ) := by
  letI : PreInnerProductSpace.Core ℂ (WeightedTwoSection E g μ hμ h hh φ hφ) :=
    weightedTwoFormPreInner E g μ hμ h hh φ hφ
  exact InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance weightedTwoSectionInnerProductSpace :
    InnerProductSpace ℂ (WeightedTwoSection E g μ hμ h hh φ hφ) :=
  InnerProductSpace.ofCore (weightedTwoFormPreInner E g μ hμ h hh φ hφ)

def WeightedTwoSection.toForm (u : WeightedTwoSection E g μ hμ h hh φ hφ) : NQForm E 2 := u.1

theorem WeightedTwoSection.toForm_weightedL2 (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    WeightedL2 (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ) := u.2

theorem WeightedTwoSection.toForm_sub (u v : WeightedTwoSection E g μ hμ h hh φ hφ) :
    (u - v).toForm E g μ hμ h hh φ hφ =
      u.toForm E g μ hμ h hh φ hφ - v.toForm E g μ hμ h hh φ hφ := rfl

theorem weightedTwoSection_inner_eq (u v : WeightedTwoSection E g μ hμ h hh φ hφ) :
    inner ℂ u v = weightedTwoInner E g.form μ h φ
      (u.toForm E g μ hμ h hh φ hφ) (v.toForm E g μ hμ h hh φ hφ) := rfl

theorem weightedTwoSection_norm_sq (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    ‖u‖ ^ 2 = (weightedNormSq (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ)).toReal := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), weightedTwoSection_inner_eq]
  change (weightedTwoInner E g.form μ h φ u.1 u.1).re = (weightedNormSq (r := r) E g.form h μ φ u.1).toReal
  have hp := weightedTwoPairing_integrable E g μ hμ h hh φ hφ u.1 u.1 u.2 u.2
  have hr : (weightedTwoInner E g.form μ h φ u.1 u.1).re =
      ∫ x, BundleDbar.formNormSq (r := r) E g.form h u.1 x * Real.exp (-φ x) ∂μ := by
    calc
      _ = ∫ x, (weightedTwoPairing E g.form h φ u.1 u.1 x).re ∂μ := by
        simpa only [weightedTwoInner, RCLike.re_eq_complex_re] using (integral_re (𝕜 := ℂ) hp).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => weightedTwoPairing_self_re (r := r) E g.form h φ u.1 x)
  rw [hr, weightedNormSq_two_eq_ofReal_integral E g μ hμ h hh φ hφ u.1 u.2,
    ENNReal.toReal_ofReal (integral_nonneg fun x =>
      mul_nonneg (formNormSq_two_nonneg E g.form h u.1 x) (Real.exp_pos _).le)]


/-- Separated completion of the actual finite weighted top forms.
Representing its arbitrary points by tensor sections remains a separate obligation. -/
abbrev WeightedTwoHilbert := UniformSpace.Completion (WeightedTwoSection E g μ hμ h hh φ hφ)

def realizeWeightedTwoSection (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    WeightedTwoHilbert E g μ hμ h hh φ hφ := u

theorem realizeWeightedTwoSection_inner (u v : WeightedTwoSection E g μ hμ h hh φ hφ) :
    inner ℂ (realizeWeightedTwoSection E g μ hμ h hh φ hφ u)
      (realizeWeightedTwoSection E g μ hμ h hh φ hφ v) =
        weightedTwoInner E g.form μ h φ (u.toForm E g μ hμ h hh φ hφ) (v.toForm E g μ hμ h hh φ hφ) :=
  UniformSpace.Completion.inner_coe u v

theorem realizeWeightedTwoSection_norm_sq (u : WeightedTwoSection E g μ hμ h hh φ hφ) :
    ‖realizeWeightedTwoSection E g μ hμ h hh φ hφ u‖ ^ 2 =
      (weightedNormSq (r := r) E g.form h μ φ (u.toForm E g μ hμ h hh φ hφ)).toReal := by
  rw [realizeWeightedTwoSection, UniformSpace.Completion.norm_coe, weightedTwoSection_norm_sq]

theorem realizeWeightedTwoSection_denseRange : DenseRange (realizeWeightedTwoSection E g μ hμ h hh φ hφ) :=
  UniformSpace.Completion.denseRange_coe

theorem weightedTwoHilbert_complete : CompleteSpace (WeightedTwoHilbert E g μ hμ h hh φ hφ) := inferInstance

end Yau.LeafProofs.L14Aux
