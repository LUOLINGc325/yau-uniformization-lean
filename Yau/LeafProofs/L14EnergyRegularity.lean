import Yau.LeafProofs.L14BKNPointwise

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

theorem continuous_of_bundle_chart (P : M.Carrier → ℝ)
    (Q : M.Carrier → ComplexVector n → ℝ)
    (hQ : ∀ a, ContinuousOn (Q a) (localDomain (r := r) E a))
    (he : ∀ a z, z ∈ localDomain (r := r) E a → P (chartInv a z) = Q a z) :
    Continuous P := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hself : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hself.2
  have hlocal := (hQ x).continuousAt ((localDomain_isOpen E x).mem_nhds hz)
  have hchart : ContinuousAt (chartPt x) x :=
    (continuousOn_extChartAt (I := ComplexModel n) x).continuousAt
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hself.1)
  have hEq : P =ᶠ[𝓝 x] (fun y => Q x (chartPt x y)) := by
    filter_upwards [(bundleChartSource_isOpen (r := r) E x).mem_nhds hself] with y hy
    have hzy : chartPt x y ∈ localDomain (r := r) E x := by
      refine ⟨(extChartAt (ComplexModel n) x).map_source hy.1, ?_⟩
      change chartInv x (chartPt x y) ∈ (localTriv (r := r) E x).baseSet
      rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)]
      exact hy.2
    have hp := he x (chartPt x y) hzy
    rw [chartInv_chartPt_of_mem x y (by simpa only [extChartAt_source] using hy.1)] at hp
    exact hp
  exact (hlocal.comp hchart).congr_of_eventuallyEq hEq

theorem chartPositiveEnergy_continuousOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u) (a : M.Carrier) :
    ContinuousOn (chartPositiveEnergy (r := r) E g.form h φ u a) (localDomain (r := r) E a) := by
  let O := localDomain (r := r) E a
  let G := hMat g.form a
  let K := weightedMetricMatrix (BundleDbar.metricMatrix (r := r) E h a) (inChart a φ)
  let D := raisedBarTensor (r := r) E g.form u a
  have hG : ContinuousOn G O := continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j =>
    ((L18Aux.hMat_contDiffOn g a i j).mono Set.inter_subset_left).continuousOn))
  have hiG : ContinuousOn (fun z => (G z)⁻¹) O := continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j =>
    ((L18Aux.hMat_inverse_contDiffOn g a i j).mono Set.inter_subset_left).continuousOn))
  have hK (α β : Fin r) : ContinuousOn (fun z => K z α β) O :=
    (weightedMetricMatrix_contDiffOn _ _ (hh a) ((hφ a).mono Set.inter_subset_left) α β).continuousOn
  have hD (α : Fin r) : ContinuousOn (fun z => D z α) O :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j =>
      (wirtBar_contDiffOn (localDomain_isOpen E a) _
        (raisedOneCoefficientsMatrix_contDiffOn E g u hu a j α) (stdVec i)).continuousOn))
  have htrace (α β : Fin r) : ContinuousOn
      (fun z => ((D z α)ᴴ * (G z)⁻¹ * D z β * (G z)ᵀ).trace) O :=
    continuous_id.matrix_trace.comp_continuousOn
      ((((continuous_id.matrix_conjTranspose.comp_continuousOn (hD α)).mul hiG).mul (hD β)).mul
        (continuous_id.matrix_transpose.comp_continuousOn hG))
  have hP : ContinuousOn (fun z => positiveTensorContraction (G z) (K z) (D z)) O := by
    apply continuousOn_finset_sum
    intro α _
    apply continuousOn_finset_sum
    intro β _
    exact (hK α β).mul (htrace α β)
  have hd : ContinuousOn (fun z => ((G z).det.re)⁻¹) O :=
    (Complex.continuous_re.comp_continuousOn
      (continuous_id.matrix_det.comp_continuousOn hG)).inv₀
      (fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz.1))
  exact hd.mul (Complex.continuous_re.comp_continuousOn hP)

theorem positiveFormEnergy_continuous (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u) :
    Continuous (positiveFormEnergy (r := r) E g.form h φ u) :=
  continuous_of_bundle_chart E _ _ (chartPositiveEnergy_continuousOn E g h hh φ hφ u hu)
    (positiveFormEnergy_inChart E hE g h φ u hu)

theorem coefficients_eq_zero_of_value_zero {q : ℕ} (u : NQForm E q)
    (a : M.Carrier) (z : ComplexVector n)
    (hz : u (chartInv a z) = (0 : NQForm E q) (chartInv a z)) (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E u a z I α = 0 := by
  unfold coefficients
  rw [hz]
  simp only [nqForm_zero_apply, ContinuousMultilinearMap.zero_apply, AlternatingMap.zero_apply,
    map_zero, PiLp.zero_apply]

theorem positiveFormEnergy_eq_zero_off_support (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier)
    (hx : x ∉ closure {y | u y ≠ (0 : NQForm E 1) y}) :
    positiveFormEnergy (r := r) E g h φ u x = 0 := by
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hInv : chartInv x z = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hnear : ∀ᶠ y in 𝓝 x, u y = (0 : NQForm E 1) y := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hn
    exact hy (subset_closure hn)
  have hCont : ContinuousAt (chartInv x) z := continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  have heq : raisedOneCoefficientsMatrix (r := r) E g u x =ᶠ[𝓝 z] (fun _ => 0) := by
    have ht := hCont.tendsto.eventually (show ∀ᶠ y in 𝓝 (chartInv x z), u y = (0 : NQForm E 1) y by
      rw [hInv]; exact hnear)
    filter_upwards [ht] with w hw
    have hF : oneCoefficientsMatrix (r := r) E u x w = 0 := by
      ext i α
      exact coefficients_eq_zero_of_value_zero E u x w hw (fun _ => i) α
    simp only [raisedOneCoefficientsMatrix, hF, Matrix.mul_zero]
  have hD : raisedBarTensor (r := r) E g u x z = 0 := by
    funext α i j
    have he := rectangularWirtBar_congr _ _ z heq i
    have ht := congrArg (fun A : Matrix (Fin n) (Fin r) ℂ => A j α) he
    simpa [raisedBarTensor, rectangularWirtBar, wirtBar] using ht
  simp only [positiveFormEnergy, chartPositiveEnergy, z, hD, positiveTensorContraction,
    Pi.zero_apply, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
    mul_zero, Finset.sum_const_zero, Complex.zero_re]

def curvatureFormEnergy (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (x : M.Carrier) : ℝ :=
  curvatureEnergy (r := r) E g h φ x
    (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α) * Real.exp (-φ x)

theorem curvatureFormEnergy_inChart (hE : Holomorphic (r := r) E) (g : HermitianField M)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    curvatureFormEnergy (r := r) E g h φ u (chartInv a z) =
      ((hMat g a z).det.re)⁻¹ *
        nakanoQuadratic (weightedCurvature (r := r) E h φ a z)
          (fun i α => raisedOneCoefficientsMatrix (r := r) E g u a z i α) *
          Real.exp (-φ (chartInv a z)) := by
  rw [curvatureFormEnergy, curvatureEnergy_inChart E hE g h hh φ hφ u a z hz]
  rfl

theorem curvatureFormEnergy_continuous (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u) :
    Continuous (curvatureFormEnergy (r := r) E g.form h φ u) := by
  apply continuous_of_bundle_chart E _ _ _ (curvatureFormEnergy_inChart E hE g.form h hh φ hφ u)
  intro a
  let O := localDomain (r := r) E a
  have hR (i j : Fin n) (α β : Fin r) : ContinuousOn
      (fun z => weightedCurvature (r := r) E h φ a z i j α β) O :=
    (weightedCurvature_contDiffOn E h hh φ hφ a i j α β).continuousOn
  have hW (i : Fin n) (α : Fin r) : ContinuousOn
      (fun z => raisedOneCoefficientsMatrix (r := r) E g.form u a z i α) O :=
    (raisedOneCoefficientsMatrix_contDiffOn E g u hu a i α).continuousOn
  have hN : ContinuousOn (fun z => nakanoQuadratic (weightedCurvature (r := r) E h φ a z)
      (fun i α => raisedOneCoefficientsMatrix (r := r) E g.form u a z i α)) O := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    apply continuousOn_finset_sum
    intro α _
    apply continuousOn_finset_sum
    intro β _
    exact ((hR i j α β).mul (hW j α).star).mul (hW i β)
  have hd : ContinuousOn (fun z => ((hMat g.form a z).det.re)⁻¹) O :=
    (Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn).inv₀
      (fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz)) |>.mono Set.inter_subset_left
  exact (hd.mul hN).mul (((hφ a).neg.exp).continuousOn.mono Set.inter_subset_left)

theorem curvatureFormEnergy_eq_zero_of_value_zero (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier)
    (hx : u x = (0 : NQForm E 1) x) : curvatureFormEnergy (r := r) E g h φ u x = 0 := by
  have hF (i : Fin n) (α : Fin r) :
      coefficients (r := r) E u x (chartPt x x) (fun _ => i) α = 0 := by
    rw [coefficients_at_chartPt E u x x (mem_extChartAt_source x), hx]
    simp only [nqForm_zero_apply, ContinuousMultilinearMap.zero_apply, AlternatingMap.zero_apply,
      map_zero, PiLp.zero_apply]
  simp only [curvatureFormEnergy, curvatureEnergy, hF, mul_zero, Finset.sum_const_zero,
    nakanoQuadratic, star_zero, Pi.zero_apply, Complex.zero_re, zero_mul]

theorem positiveFormEnergy_hasCompactSupport (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    HasCompactSupport (positiveFormEnergy (r := r) E g h φ u) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (positiveFormEnergy_eq_zero_off_support E g h φ u x hn)

theorem curvatureFormEnergy_hasCompactSupport (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    HasCompactSupport (curvatureFormEnergy (r := r) E g h φ u) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  by_contra hn
  exact hx (curvatureFormEnergy_eq_zero_of_value_zero E g h φ u x (not_not.mp hn))

def bknResidual (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (f : NQForm E 2) (S : NQForm E 0) (x : M.Carrier) : ℝ :=
  bknDifferentialEnergy (r := r) E g h φ u f S x - curvatureFormEnergy (r := r) E g h φ u x

theorem weighted_formNormSq_integrable_of_continuous {q : ℕ}
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E q)
    (hu : Continuous (BundleDbar.formNormSq (r := r) E g.form h u))
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E q) x})) :
    Integrable (fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  have hs : Function.support (fun x => BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x)) ⊆
      {x | u x ≠ (0 : NQForm E q) x} := by
    intro x hx hz
    apply hx
    change BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-φ x) = 0
    rw [formNormSq_congr_at E g.form h u (0 : NQForm E q) x hz, formNormSq_zero, zero_mul]
  exact (hu.mul (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg)).integrable_of_hasCompactSupport
    (hc.of_isClosed_subset isClosed_closure (closure_mono hs))

theorem positiveFormEnergy_integrable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    Integrable (positiveFormEnergy (r := r) E g.form h φ u) μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  exact (positiveFormEnergy_continuous E hE g h hh φ hφ u hu).integrable_of_hasCompactSupport
    (positiveFormEnergy_hasCompactSupport E g.form h φ u hc)

theorem curvatureFormEnergy_integrable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    Integrable (curvatureFormEnergy (r := r) E g.form h φ u) μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  exact (curvatureFormEnergy_continuous E hE g h hh φ hφ u hu).integrable_of_hasCompactSupport
    (curvatureFormEnergy_hasCompactSupport E g.form h φ u hc)

theorem bknResidual_integrable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hcu : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x}))
    (f : NQForm E 2) (hf : SmoothForm (r := r) E f)
    (hcf : IsCompact (closure {x | f x ≠ (0 : NQForm E 2) x}))
    (S : NQForm E 0) (hS : SmoothForm (r := r) E S)
    (hcS : IsCompact (closure {x | S x ≠ (0 : NQForm E 0) x})) :
    Integrable (bknResidual (r := r) E g.form h φ u f S) μ :=
  (((weighted_formNormSq_integrable_of_continuous E g μ hμ h φ hφ f
      (formNormSq_two_continuous E g h hh f hf) hcf).add
    (weighted_formNormSq_integrable_of_continuous E g μ hμ h φ hφ S
      (formNormSq_top_continuous E g h hh S hS) hcS)).sub
    (positiveFormEnergy_integrable E hE g μ hμ h hh φ hφ u hu hcu)).sub
    (curvatureFormEnergy_integrable E hE g μ hμ h hh φ hφ u hu hcu)

end Yau.LeafProofs.L14Aux
