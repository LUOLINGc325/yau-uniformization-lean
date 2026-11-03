import Yau.LeafProofs.L14CurvatureEnergy
import Yau.LeafProofs.L14Localize

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

theorem exists_oneForm_with_chart_coefficients (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) (V : Fin n → Fin r → ℂ) :
    ∃ u : NQForm E 1, (fun i α => coefficients (r := r) E u a z (fun _ => i) α) = V := by
  refine ⟨oneFormPushforward (r := r) E a (fun _ i => WithLp.toLp 2 (V i)), ?_⟩
  funext i α
  exact oneFormPushforward_coefficients E a (fun _ i => WithLp.toLp 2 (V i)) z hz i α

theorem oneFormPairing_chart_matrix (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 1) (a : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ localDomain (r := r) E a) :
    oneFormPairing E g h u v (chartInv a z) =
      (((hMat g a z).det.re)⁻¹ : ℝ) *
        matrixCoefficientPairing (BundleDbar.metricMatrix (r := r) E h a z)
          (fun i α => coefficients (r := r) E u a z (fun _ => i) α)
          ((hMat g a z)⁻¹ * Matrix.of
            (fun i α => coefficients (r := r) E v a z (fun _ => i) α)) := by
  rw [oneFormPairing_inChart E g h u v a z hz, ← coefficient_contraction_assoc]
  simp only [Complex.ofReal_inv, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- The original variational inverse-curvature norm in an arbitrary bundle chart.
No regularity of the source form is used in this identity. -/
theorem inverseCurvatureNormSq_inChart (hE : Holomorphic (r := r) E)
    (g : HermitianField M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (f : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    inverseCurvatureNormSq (r := r) E g h φ f (chartInv a z) =
      ENNReal.ofReal (((hMat g a z).det.re)⁻¹) *
        chartInverseCurvatureCoefficientSup (r := r) E h φ f a z := by
  let x := chartInv a z
  let G := hMat g a z
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let R := weightedCurvature (r := r) E h φ a z
  let F := fun i α => coefficients (r := r) E f a z (fun _ => i) α
  let C := fun u : NQForm E 1 =>
    fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α
  let A := fun u : NQForm E 1 =>
    fun i α => coefficients (r := r) E u a z (fun _ => i) α
  let d := (G.det.re)⁻¹
  let P := fun U : Fin n → Fin r → ℂ => ENNReal.ofReal
    (2 * (matrixCoefficientPairing H F U).re - nakanoQuadratic R U)
  have hG : G.PosDef := hMat_posDef g a z hz.1
  have hd : 0 ≤ d := inv_nonneg.mpr (Complex.nonneg_iff.mp hG.posSemidef.det_nonneg).1
  have hterm (u : NQForm E 1) :
      ENNReal.ofReal (2 * (coefficientInner (r := r) E g h x (C f) (C u)).re -
        curvatureEnergy (r := r) E g h φ x (C u)) =
          ENNReal.ofReal d * P (G⁻¹ * Matrix.of (A u)) := by
    change ENNReal.ofReal (2 * (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α)
      (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α)).re -
      curvatureEnergy (r := r) E g h φ x
        (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α)) = _
    rw [← oneFormPairing_eq_coefficientInner E g h f u x,
      oneFormPairing_chart_matrix E g h f u a z hz,
      curvatureEnergy_inChart E hE g h hh φ hφ u a z hz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← ENNReal.ofReal_mul hd]
    congr 1
    change 2 * (d * (matrixCoefficientPairing H F (G⁻¹ * Matrix.of (A u))).re) -
      d * nakanoQuadratic R (G⁻¹ * Matrix.of (A u)) =
        d * (2 * (matrixCoefficientPairing H F (G⁻¹ * Matrix.of (A u))).re -
          nakanoQuadratic R (G⁻¹ * Matrix.of (A u)))
    ring
  have hxself : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  change (⨆ V : Fin n → Fin r → ℂ, ENNReal.ofReal
    (2 * (coefficientInner (r := r) E g h x (C f) V).re -
      curvatureEnergy (r := r) E g h φ x V)) = ENNReal.ofReal d * ⨆ U, P U
  rw [ENNReal.mul_iSup]
  apply le_antisymm
  · apply iSup_le
    intro V
    obtain ⟨u, hu⟩ := exists_oneForm_with_chart_coefficients E x (chartPt x x) hxself V
    have ht := hterm u
    change C u = V at hu
    rw [hu] at ht
    rw [ht]
    exact le_iSup (fun U => ENNReal.ofReal d * P U) (G⁻¹ * Matrix.of (A u))
  · apply iSup_le
    intro U
    obtain ⟨u, hu⟩ := exists_oneForm_with_chart_coefficients E a z hz (G * Matrix.of U)
    change A u = G * Matrix.of U at hu
    have hraise : G⁻¹ * Matrix.of (A u) = Matrix.of U := by
      rw [hu]
      change G⁻¹ * (G * Matrix.of U) = Matrix.of U
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (hG.isUnit.map Matrix.detMonoidHom), Matrix.one_mul]
    have ht := hterm u
    rw [hraise] at ht
    change ENNReal.ofReal d * P (Matrix.of U) ≤ _
    rw [← ht]
    exact le_iSup (fun V => ENNReal.ofReal
      (2 * (coefficientInner (r := r) E g h x (C f) V).re -
        curvatureEnergy (r := r) E g h φ x V)) (C u)

/-- Descent of extended nonnegative measurable functions through a countable
bundle atlas and the original Riemannian-volume chart formula. -/
theorem aemeasurable_ennreal_of_bundleCharts (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (F : M.Carrier → ℝ≥0∞)
    (hF : ∀ a, AEMeasurable (fun z => F (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a))) : AEMeasurable F μ := by
  have hlocal (a : M.Carrier) :
      AEMeasurable F (μ.restrict (bundleChartSource (r := r) E a)) := by
    have ht := (hF a).comp_quasiMeasurePreserving
      (chartPtExtension_quasiMeasurePreserving (r := r) E g μ hμ a)
    apply ht.congr
    filter_upwards [ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet] with x hx
    change F (chartInv a (chartPtExtension a x)) = F x
    rw [chartPtExtension, ite_eq_left hx.1,
      chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)]
  obtain ⟨v, hv⟩ := isLindelof_univ.indexed_countable_subcover (bundleChartSource (r := r) E)
    (bundleChartSource_isOpen (r := r) E) (by
      intro y _
      exact Set.mem_iUnion.mpr
        ⟨y, mem_extChartAt_source y, FiberBundle.mem_baseSet_trivializationAt' y⟩)
  have hcover : (⋃ j, bundleChartSource (r := r) E (v j)) = Set.univ :=
    Set.eq_univ_of_univ_subset hv
  have hm := AEMeasurable.iUnion (fun j => hlocal (v j))
  simpa only [hcover, Measure.restrict_univ] using hm

/-- The actual inverse-curvature function is measurable in each fixed chart
for a merely locally L² source. -/
theorem inverseCurvatureNormSq_inChart_aemeasurable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (f : NQForm E 1)
    (hf : LocallyL2 (r := r) E f) (a : M.Carrier) :
    AEMeasurable (fun z => inverseCurvatureNormSq (r := r) E g.form h φ f (chartInv a z))
      ((lebesgueC n).restrict (localDomain (r := r) E a)) := by
  have hd : ContinuousOn (fun z => (hMat g.form a z).det.re) (chartTarget a) :=
    Complex.continuous_re.comp_continuousOn
      (L18Aux.contDiffOn_matrix_det (L18Aux.hMat_contDiffOn g a)).continuousOn
  have hdi := (hd.inv₀ fun z hz => ne_of_gt (L18Aux.hMat_det_re_pos g.form a hz)).mono
    (show localDomain (r := r) E a ⊆ chartTarget a from Set.inter_subset_left)
  have hdm : AEMeasurable (fun z => ((hMat g.form a z).det.re)⁻¹)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) :=
    (hdi.aestronglyMeasurable (localDomain_isOpen E a).measurableSet).aemeasurable
  have hm := (ENNReal.measurable_ofReal.comp_aemeasurable hdm).mul
    (chartInverseCurvatureCoefficientSup_aemeasurable E h hh φ hφ f hf a)
  apply hm.congr
  filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
  exact (inverseCurvatureNormSq_inChart E hE g.form h hh φ hφ f a z hz).symm

/-- Global measurability of the original inverse norm requires only the
original local-L² hypothesis on the source. -/
theorem inverseCurvatureNormSq_aemeasurable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (f : NQForm E 1)
    (hf : LocallyL2 (r := r) E f) :
    AEMeasurable (inverseCurvatureNormSq (r := r) E g.form h φ f) μ := by
  exact aemeasurable_ennreal_of_bundleCharts E g.form μ hμ _
    (fun a => inverseCurvatureNormSq_inChart_aemeasurable E hE g h hh φ hφ f hf a)

/-- The weighted inverse-curvature energy integrand from the original root
is measurable, without a global weighted-L² assumption on the source. -/
theorem weighted_inverseCurvatureNormSq_aemeasurable (hE : Holomorphic (r := r) E)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (f : NQForm E 1)
    (hf : LocallyL2 (r := r) E f) :
    AEMeasurable (fun x => inverseCurvatureNormSq (r := r) E g.form h φ f x *
      ENNReal.ofReal (Real.exp (-φ x))) μ := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable
  exact (inverseCurvatureNormSq_aemeasurable E hE g μ hμ h hh φ hφ f hf).mul hw.aemeasurable

end Yau.LeafProofs.L14Aux
