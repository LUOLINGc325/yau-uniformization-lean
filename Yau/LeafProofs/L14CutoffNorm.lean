import Yau.LeafProofs.L14AdjointWeak

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem formNormSq_multiply_real_one (g : HermitianField M) (h : Metric E)
    (χ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E g h (multiplyForm E (fun x => (χ x : ℂ)) u) x =
      χ x ^ 2 * BundleDbar.formNormSq (r := r) E g h u x := by
  have he : multiplyForm E (fun x => (χ x : ℂ)) u x = ((χ x : ℂ) • u) x := by
    apply Subtype.ext
    rfl
  rw [formNormSq_congr_at E g h _ _ x he, formNormSq_one_smul]
  simp only [Complex.normSq_ofReal, pow_two]

theorem weightedL2_multiply_real_one (g : HermitianField M) (μ : Measure M.Carrier)
    (h : Metric E) (φ : M.Carrier → ℝ) (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (u : NQForm E 1) (hu : WeightedL2 (r := r) E g h μ φ u)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, χ x ^ 2 ≤ C) :
    WeightedL2 (r := r) E g h μ φ (multiplyForm E (fun x => (χ x : ℂ)) u) := by
  have hη (a : M.Carrier) : ContinuousOn (inChart a (fun x => (χ x : ℂ))) (localDomain (r := r) E a) :=
    (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).continuousOn.mono Set.inter_subset_left)
  refine ⟨locallyL2_multiplyForm E (fun x => (χ x : ℂ)) hη u hu.1, ?_⟩
  have hn (x : M.Carrier) : 0 ≤ BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x) :=
    mul_nonneg (formNormSq_one_nonneg E g h u x) (Real.exp_pos _).le
  have hle : weightedNormSq (r := r) E g h μ φ (multiplyForm E (fun x => (χ x : ℂ)) u) ≤
      ENNReal.ofReal C * weightedNormSq (r := r) E g h μ φ u := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (C * (BundleDbar.formNormSq (r := r) E g h u x * Real.exp (-φ x))) ∂μ := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (BundleDbar.formNormSq (r := r) E g h
          (multiplyForm E (fun x => (χ x : ℂ)) u) x * Real.exp (-φ x)) ≤ _
        rw [formNormSq_multiply_real_one]
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound x) (hn x)
      _ = _ := by
        simp only [ENNReal.ofReal_mul hC]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2)

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

def weightedOneCutoffSection (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) (U : WeightedOneSection E g μ hμ h hh φ hφ) :
    WeightedOneSection E g μ hμ h hh φ hφ :=
  ⟨multiplyForm E (fun x => (χ x : ℂ)) U.1,
    weightedL2_multiply_real_one E g.form μ h φ χ hχ U.1 U.2 1 (by norm_num)
      (fun x => by have h0 := (hbound x).1; have h1 := (hbound x).2; nlinarith)⟩

theorem realizeWeightedOneSection_sub
    (V U : WeightedOneSection E g μ hμ h hh φ hφ) :
    realizeWeightedOneSection E g μ hμ h hh φ hφ (V - U) =
      realizeWeightedOneSection E g μ hμ h hh φ hφ V - realizeWeightedOneSection E g μ hμ h hh φ hφ U :=
  map_sub (UniformSpace.Completion.toCompl : WeightedOneSection E g μ hμ h hh φ hφ →+
    WeightedOneHilbert E g μ hμ h hh φ hφ) V U

theorem weightedOneCutoffSection_sub_val
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hbound : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (U : WeightedOneSection E g μ hμ h hh φ hφ) :
    (weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U - U).1 =
      multiplyForm E (fun x => ((χ x - 1 : ℝ) : ℂ)) U.1 := by
  have he := WeightedOneSection.toForm_sub E g μ hμ h hh φ hφ
    (weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U) U
  change (weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U - U).1 =
    (weightedOneCutoffSection E g μ hμ h hh φ hφ χ hχ hbound U).1 - U.1 at he
  rw [he]
  funext x
  apply Subtype.ext
  change (χ x : ℂ) • (U.1 x).1 - (U.1 x).1 = ((χ x - 1 : ℝ) : ℂ) • (U.1 x).1
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  simpa only [one_smul] using (sub_smul (χ x : ℂ) 1 (U.1 x).1).symm

theorem weightedOneCutoffSection_tendsto
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m, SmoothFn (χ m))
    (hbound : ∀ m x, χ m x ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ∀ x, ∀ᶠ m in atTop, χ m x = 1)
    (U : WeightedOneSection E g μ hμ h hh φ hφ) :
    Tendsto (fun m => realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedOneCutoffSection E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U))
      atTop (𝓝 (realizeWeightedOneSection E g μ hμ h hh φ hφ U)) := by
  let V := fun m => weightedOneCutoffSection E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U
  let B := fun x => BundleDbar.formNormSq (r := r) E g.form h U.1 x * Real.exp (-φ x)
  let F := fun m x => (χ m x - 1) ^ 2 * B x
  have hB : Integrable B μ := weightedOneNorm_integrable E g μ hμ h hh φ hφ U.1 U.2
  have hnB (x : M.Carrier) : 0 ≤ B x :=
    mul_nonneg (formNormSq_one_nonneg E g.form h U.1 x) (Real.exp_pos _).le
  have hnF (m : ℕ) (x : M.Carrier) : 0 ≤ F m x := mul_nonneg (sq_nonneg _) (hnB x)
  have hFm (m : ℕ) : AEStronglyMeasurable (F m) μ :=
    (((L18Aux.continuous_of_smoothFn (hχ m)).sub continuous_const).pow 2).aestronglyMeasurable.mul hB.aestronglyMeasurable
  have hFlim : Tendsto (fun m => ∫ x, F m x ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence B hFm hB
      (fun m => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hnF m x)]
        have h0 := (hbound m x).1
        have h1 := (hbound m x).2
        have hs : (χ m x - 1) ^ 2 ≤ 1 := by nlinarith
        exact mul_le_of_le_one_left (hnB x) hs)
      (Eventually.of_forall fun x => by
        have he : (fun m => F m x) =ᶠ[atTop] (fun _ => 0) :=
          (hpoint x).mono (fun m hm => by simp only [F, hm, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul])
        exact tendsto_const_nhds.congr' he.symm)
    simpa only [integral_zero] using ht
  have hsq (m : ℕ) :
      ‖realizeWeightedOneSection E g μ hμ h hh φ hφ (V m) -
        realizeWeightedOneSection E g μ hμ h hh φ hφ U‖ ^ 2 = ∫ x, F m x ∂μ := by
    rw [← realizeWeightedOneSection_sub E g μ hμ h hh φ hφ, realizeWeightedOneSection_norm_sq]
    change (weightedNormSq (r := r) E g.form h μ φ (V m - U).1).toReal = _
    rw [weightedNormSq_one_eq_ofReal_integral E g μ hμ h hh φ hφ (V m - U).1 (V m - U).2]
    have hfun (x : M.Carrier) : BundleDbar.formNormSq (r := r) E g.form h (V m - U).1 x * Real.exp (-φ x) = F m x := by
      rw [weightedOneCutoffSection_sub_val E g μ hμ h hh φ hφ (χ m) (hχ m) (hbound m) U,
        formNormSq_multiply_real_one]
      simp only [F, B]
      ring
    simp_rw [hfun]
    exact ENNReal.toReal_ofReal (integral_nonneg (hnF m))
  have hpow : Tendsto (fun m => ‖realizeWeightedOneSection E g μ hμ h hh φ hφ (V m) -
      realizeWeightedOneSection E g μ hμ h hh φ hφ U‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hFlim
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hpow
  simp only [Real.sqrt_zero] at hnorm
  have hnorm' : Tendsto (fun m => ‖realizeWeightedOneSection E g μ hμ h hh φ hφ (V m) -
      realizeWeightedOneSection E g μ hμ h hh φ hφ U‖) atTop (𝓝 0) := by
    convert hnorm using 1
    funext m
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm'

end Yau.LeafProofs.L14Aux
