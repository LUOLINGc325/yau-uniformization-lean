import Yau.LeafProofs.L14OperatorLocality

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

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem smooth_adjoint_output_unique
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (S R : WeightedTopSection E g μ hμ h hh φ hφ)
    (hS : SmoothForm (r := r) E S.1) (hR : SmoothForm (r := r) E R.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (hUR : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ R) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) : S.1 = R.1 := by
  apply topForm_ext (r := r) E
  intro a z hz
  exact (smooth_adjoint_local_formula E g μ hμ h hh φ hφ hE U S hU hS hUS a z hz).trans
    (smooth_adjoint_local_formula E g μ hμ h hh φ hφ hE U R hU hR hUR a z hz).symm

include hE in
theorem compact_adjoint_multiplier_output_eq
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (S : WeightedTopSection E g μ hμ h hh φ hφ) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (V : WeightedOneSection E g μ hμ h hh φ hφ)
    (hV : V.1 = multiplyForm E (fun x => (χ x : ℂ)) U.1)
    (R : WeightedTopSection E g μ hμ h hh φ hφ) (hR : SmoothForm (r := r) E R.1)
    (hVR : (realizeWeightedOneSection E g μ hμ h hh φ hφ V,
      realizeWeightedTopSection E g μ hμ h hh φ hφ R) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) :
    R.1 = multiplyForm E (fun x => (χ x : ℂ)) S.1 - scalarGradientContraction (r := r) E g.form χ U.1 := by
  let v := multiplyForm E (fun x => (χ x : ℂ)) U.1
  have hv := smoothForm_multiply_real (r := r) E χ hχ U.1 hU
  have hvc := compact_formSupport_multiply E χ hcχ U.1
  let V0 : WeightedOneSection E g μ hμ h hh φ hφ :=
    ⟨v, smooth_compact_weightedL2_one E g μ hμ h hh φ hφ v hv hvc⟩
  have hV0 : V = V0 := Subtype.ext hV
  obtain ⟨R0, hR0, hcR0, hVR0, hEq⟩ :=
    smooth_compact_adjoint_multiplier E g μ hμ h hh φ hφ hE U S hU hS hUS χ hχ hcχ
  have hVR0' : (realizeWeightedOneSection E g μ hμ h hh φ hφ V,
      realizeWeightedTopSection E g μ hμ h hh φ hφ R0) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
    rw [hV0]
    exact hVR0
  have hVs : SmoothForm (r := r) E V.1 := by rw [hV]; exact hv
  exact (smooth_adjoint_output_unique E g μ hμ h hh φ hφ hE V hVs R R0 hR hR0 hVR hVR0').trans hEq

include hE in
theorem compact_bkn_residual_integral_zero
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (hcU : IsCompact (closure {x | U.1 x ≠ (0 : NQForm E 1) x}))
    (f : NQForm E 2) (hdu : SmoothDbarRepresents (r := r) E U.1 f)
    (S : WeightedTopSection E g μ hμ h hh φ hφ) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) :
    (∫ x, bknResidual (r := r) E g.form h φ U.1 f S.1 x ∂μ) = 0 := by
  classical
  let K := closure {x | U.1 x ≠ (0 : NQForm E 1) x}
  obtain ⟨s, χ, hχ, hχn, hχs, hχone⟩ := exists_finite_smooth_bundle_square_partition (r := r) E g hcU
  let F := fun i : s => compactOneChartCoefficients (r := r) E (χ i) U.1 (i : M.Carrier)
  have hF (i : s) : ContDiff ℝ ∞ (F i) ∧ HasCompactSupport (F i) ∧
      tsupport (F i) ⊆ localDomain (r := r) E (i : M.Carrier) :=
    compactOneChartCoefficients_properties E (χ i) (hχ i).1 (hχ i).2 U.1 hU (i : M.Carrier) (hχs i)
  let V := fun i : s => weightedOneChartSection E g μ hμ h hh φ hφ hE (i : M.Carrier)
    (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  let R := fun i : s => weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE (i : M.Carrier)
    (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  let fχ := fun i : s => twoFormPushforward (r := r) E (i : M.Carrier) (modelOneDbar (F i))
  have hV (i : s) : (V i).1 = multiplyForm E (fun x => (χ i x : ℂ)) U.1 :=
    (multiplyForm_eq_oneFormPushforward E (χ i) U.1 (i : M.Carrier) (hχs i)).symm
  have hVs (i : s) : SmoothForm (r := r) E (V i).1 :=
    oneFormPushforward_smooth E hE (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hRs (i : s) : SmoothForm (r := r) E (R i).1 :=
    (weightedDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2).1
  have hVR (i : s) : (realizeWeightedOneSection E g μ hμ h hh φ hφ (V i),
      realizeWeightedTopSection E g μ hμ h hh φ hφ (R i)) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph :=
    weightedMaximalDbar_adjoint_chart E g μ hμ h hh φ hφ hE (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hSχ (i : s) : (R i).1 = multiplyForm E (fun x => (χ i x : ℂ)) S.1 -
      scalarGradientContraction (r := r) E g.form (χ i) U.1 :=
    compact_adjoint_multiplier_output_eq E g μ hμ h hh φ hφ hE U hU S hS hUS
      (χ i) (hχ i).1 (hχ i).2 (V i) (hV i) (R i) (hRs i) (hVR i)
  have hdV (i : s) : SmoothDbarRepresents (r := r) E (V i).1 (fχ i) :=
    oneFormPushforward_representsDbar E hE (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hdfχ (i : s) : SmoothDbarRepresents (r := r) E
      (multiplyForm E (fun x => (χ i x : ℂ)) U.1) (fχ i) := by
    rw [← hV i]
    exact hdV i
  let P := fun i : s => bknResidual (r := r) E g.form h φ (V i).1 (fχ i) (R i).1
  have hP (i : s) : Integrable (P i) μ :=
    bknResidual_oneFormPushforward_integrable E hE g μ hμ h hh φ hφ (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hPint (i : s) : (∫ x, P i x ∂μ) = 0 :=
    bknResidual_oneFormPushforward_integral_zero E hE g μ hμ h hh φ hφ (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hsum (x : M.Carrier) : (∑ i : s, P i x) = bknResidual (r := r) E g.form h φ U.1 f S.1 x := by
    by_cases hx : x ∈ K
    · have hD := finite_bknDifferentialEnergy_IMS E hE g h φ U.1 hU f hdu S.1
        χ (fun i => (hχ i).1) fχ hdfχ (fun i => (R i).1) hSχ x (hχone x hx)
      have hC : (∑ i : s, curvatureFormEnergy (r := r) E g.form h φ
          (multiplyForm E (fun x => (χ i x : ℂ)) U.1) x) =
          curvatureFormEnergy (r := r) E g.form h φ U.1 x := by
        simp_rw [curvatureFormEnergy_multiply_real E g.form h φ]
        rw [← Finset.sum_mul, (hχone x hx).self_of_nhds, one_mul]
      change (∑ i : s, (bknDifferentialEnergy (r := r) E g.form h φ (V i).1 (fχ i) (R i).1 x -
        curvatureFormEnergy (r := r) E g.form h φ (V i).1 x)) = _
      simp_rw [hV]
      rw [Finset.sum_sub_distrib, hD, hC]
      rfl
    · have hzero (i : s) : P i x = 0 := by
        apply bknResidual_eq_zero_off_support E g μ hμ h hh φ hφ hE (V i) (hVs i) (fχ i)
          (hdV i) (R i) (hRs i) (hVR i) x
        rw [hV i]
        exact fun h => hx (closure_formSupport_multiply_subset E _ U.1 h)
      rw [bknResidual_eq_zero_off_support E g μ hμ h hh φ hφ hE U hU f hdu S hS hUS x hx]
      simp only [hzero, Finset.sum_const_zero]
  calc
    _ = ∫ x, ∑ i : s, P i x ∂μ := integral_congr_ae (Eventually.of_forall fun x => (hsum x).symm)
    _ = ∑ i : s, ∫ x, P i x ∂μ := integral_finset_sum _ (fun i _ => hP i)
    _ = 0 := by simp only [hPint, Finset.sum_const_zero]

include hE in
theorem compact_bkn_integral_identity
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (hcU : IsCompact (closure {x | U.1 x ≠ (0 : NQForm E 1) x}))
    (f : NQForm E 2) (hf : SmoothForm (r := r) E f)
    (hcf : IsCompact (closure {x | f x ≠ (0 : NQForm E 2) x}))
    (hdu : SmoothDbarRepresents (r := r) E U.1 f)
    (S : WeightedTopSection E g μ hμ h hh φ hφ) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) :
    (∫ x, curvatureFormEnergy (r := r) E g.form h φ U.1 x ∂μ) +
      (∫ x, positiveFormEnergy (r := r) E g.form h φ U.1 x ∂μ) =
    (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) ∂μ) +
      ∫ x, BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) ∂μ := by
  have hiF := weighted_formNormSq_integrable_of_continuous E g μ hμ h φ hφ f
    (formNormSq_two_continuous E g h hh f hf) hcf
  have hiS := weightedTopNorm_integrable E g μ hμ h hh φ hφ S.1 S.2
  have hiP := positiveFormEnergy_integrable E hE g μ hμ h hh φ hφ U.1 hU hcU
  have hiC := curvatureFormEnergy_integrable E hE g μ hμ h hh φ hφ U.1 hU hcU
  have he := compact_bkn_residual_integral_zero E g μ hμ h hh φ hφ hE U hU hcU f hdu S hS hUS
  change (∫ x, ((BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
    BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x)) -
    positiveFormEnergy (r := r) E g.form h φ U.1 x) - curvatureFormEnergy (r := r) E g.form h φ U.1 x ∂μ) = 0 at he
  have hAdd : (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
      BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) ∂μ) =
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) ∂μ) +
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) ∂μ) :=
    integral_add hiF hiS
  have hSubP : (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
      BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) -
      positiveFormEnergy (r := r) E g.form h φ U.1 x ∂μ) =
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
        BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) ∂μ) -
      (∫ x, positiveFormEnergy (r := r) E g.form h φ U.1 x ∂μ) :=
    integral_sub (hiF.add hiS) hiP
  have hSubC : (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
      BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) -
      positiveFormEnergy (r := r) E g.form h φ U.1 x - curvatureFormEnergy (r := r) E g.form h φ U.1 x ∂μ) =
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) +
        BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) -
        positiveFormEnergy (r := r) E g.form h φ U.1 x ∂μ) -
      (∫ x, curvatureFormEnergy (r := r) E g.form h φ U.1 x ∂μ) :=
    integral_sub ((hiF.add hiS).sub hiP) hiC
  linarith


include hE in
theorem compact_bkn_estimate
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (hcU : IsCompact (closure {x | U.1 x ≠ (0 : NQForm E 1) x}))
    (f : NQForm E 2) (hf : SmoothForm (r := r) E f)
    (hcf : IsCompact (closure {x | f x ≠ (0 : NQForm E 2) x}))
    (hdu : SmoothDbarRepresents (r := r) E U.1 f)
    (S : WeightedTopSection E g μ hμ h hh φ hφ) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph) :
    (∫ x, curvatureFormEnergy (r := r) E g.form h φ U.1 x ∂μ) ≤
      (weightedNormSq (r := r) E g.form h μ φ f).toReal +
        ‖realizeWeightedTopSection E g μ hμ h hh φ hφ S‖ ^ 2 := by
  have hiF := weighted_formNormSq_integrable_of_continuous E g μ hμ h φ hφ f
    (formNormSq_two_continuous E g h hh f hf) hcf
  have hnF (x : M.Carrier) : 0 ≤ BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) :=
    mul_nonneg (formNormSq_two_nonneg E g.form h f x) (Real.exp_pos _).le
  have hnS (x : M.Carrier) : 0 ≤ BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) :=
    mul_nonneg (formNormSq_top_nonneg E g.form h S.1 x) (Real.exp_pos _).le
  have hNF : (weightedNormSq (r := r) E g.form h μ φ f).toReal =
      ∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) ∂μ := by
    rw [show weightedNormSq (r := r) E g.form h μ φ f = ENNReal.ofReal
      (∫ x, BundleDbar.formNormSq (r := r) E g.form h f x * Real.exp (-φ x) ∂μ) from
        (ofReal_integral_eq_lintegral_ofReal hiF (Eventually.of_forall hnF)).symm,
      ENNReal.toReal_ofReal (integral_nonneg hnF)]
  have hNS : ‖realizeWeightedTopSection E g μ hμ h hh φ hφ S‖ ^ 2 =
      ∫ x, BundleDbar.formNormSq (r := r) E g.form h S.1 x * Real.exp (-φ x) ∂μ := by
    rw [realizeWeightedTopSection_norm_sq]
    change (weightedNormSq (r := r) E g.form h μ φ S.1).toReal = _
    rw [weightedNormSq_top_eq_ofReal_integral E g μ hμ h hh φ hφ S.1 S.2,
      ENNReal.toReal_ofReal (integral_nonneg hnS)]
  have he := compact_bkn_integral_identity E g μ hμ h hh φ hφ hE U hU hcU f hf hcf hdu S hS hUS
  have hp : 0 ≤ ∫ x, positiveFormEnergy (r := r) E g.form h φ U.1 x ∂μ :=
    integral_nonneg (positiveFormEnergy_nonneg E g.form h φ U.1)
  rw [hNF, hNS]
  linarith

include hE in
theorem exists_compact_bkn_data
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (hcU : IsCompact (closure {x | U.1 x ≠ (0 : NQForm E 1) x})) :
    ∃ f : NQForm E 2, ∃ S : WeightedTopSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E f ∧ IsCompact (closure {x | f x ≠ (0 : NQForm E 2) x}) ∧
      SmoothDbarRepresents (r := r) E U.1 f ∧ MaximalDbarGraph (r := r) E g.form h μ φ U.1 f ∧
      SmoothForm (r := r) E S.1 ∧ IsCompact (closure {x | S.1 x ≠ (0 : NQForm E 0) x}) ∧
      (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
        realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph ∧
      (∫ x, curvatureFormEnergy (r := r) E g.form h φ U.1 x ∂μ) ≤
        (weightedNormSq (r := r) E g.form h μ φ f).toReal +
          ‖realizeWeightedTopSection E g μ hμ h hh φ hφ S‖ ^ 2 := by
  obtain ⟨f, hf, hcf, hdu, hgraph⟩ := smooth_compact_oneForm_has_dbar E g μ hμ h hh φ hφ hE U.1 hU hcU
  obtain ⟨S, hS, hcS, hUS⟩ := smooth_compact_oneForm_has_adjoint E g μ hμ h hh φ hφ hE U.1 hU hcU
  refine ⟨f, S, hf, hcf, hdu, hgraph, hS, hcS, hUS, ?_⟩
  exact compact_bkn_estimate E g μ hμ h hh φ hφ hE U hU hcU f hf hcf hdu S hS hUS

end Yau.LeafProofs.L14Aux
