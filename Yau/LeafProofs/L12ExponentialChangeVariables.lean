import Yau.LeafProofs.L12ExponentialVolume
import Yau.LeafProofs.L09
import Mathlib.MeasureTheory.Function.Jacobian

/-! Change of variables for the genuine exponential on arbitrary Borel
injectivity sets, with the genuine physical Gram density. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- Physical volume in the initial tangent fibre. -/
def realTangentVolume (g : SmoothMetric M) (x : M.Carrier) :
    @Measure (TangentSpace 𝓘(ℝ, ComplexVector n) x) (borel _) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  exact (realInitialOrthonormalFrame g x).toBasis.addHaar

private def realFrameIndex (n : ℕ) : RIdx n ≃ Fin (2 * n) :=
  Fintype.equivFinOfCardEq (by simp [RIdx, Nat.mul_comm])

/-- A physical isometry which sends the standard real coordinate vectors to
an enumeration of the actual initial orthonormal frame. -/
private def realPhysicalCoordinates (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    ComplexVector n ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) x := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact (complexVector_realOrthonormalBasis n).repr.trans
    ((realInitialOrthonormalFrame g x).reindex (realFrameIndex n).symm).repr.symm

private theorem realPhysicalCoordinates_realVec (g : SmoothMetric M) (x : M.Carrier)
    (a : RIdx n) : realPhysicalCoordinates g x (realVec a) =
      realInitialOrthonormalFrame g x (realFrameIndex n a) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  rw [← complexVector_realOrthonormalBasis_apply n a]
  simp [realPhysicalCoordinates, OrthonormalBasis.reindex_apply]

theorem realTangentVolume_isAddHaarMeasure (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
    IsAddHaarMeasure (realTangentVolume g x) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  dsimp [realTangentVolume]
  infer_instance

private theorem realPhysicalCoordinates_measurePreserving (g : SmoothMetric M) (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
    MeasurePreserving (realPhysicalCoordinates g x) volume (realTangentVolume g x) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  simpa only [realTangentVolume, OrthonormalBasis.addHaar_eq_volume] using
    (realPhysicalCoordinates g x).measurePreserving

set_option backward.isDefEq.respectTransparency false in
private theorem gram_matrix_comp {E ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) (D : E →L[ℝ] E) :
    (fun i j => B (D (b i)) (D (b j))) =
      (LinearMap.toMatrix b b D.toLinearMap)ᵀ * (show Matrix ι ι ℝ from fun i j => B (b i) (b j)) *
        LinearMap.toMatrix b b D.toLinearMap := by
  ext i j
  conv_lhs => rw [← b.sum_repr (D (b i)), ← b.sum_repr (D (b j))]
  simp only [_root_.map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
private theorem realExponentialVolumeDensity_in_chart (g : SmoothMetric M)
    (x y : M.Carrier) (u : ComplexVector n)
    (hy : realExponentialMap g x (realPhysicalCoordinates g x u) ∈
      (chartAt (ComplexVector n) y).source) :
    realExponentialVolumeDensity g x (realPhysicalCoordinates g x u) =
      |(fderiv ℝ (fun a => chartPt y
        (realExponentialMap g x (realPhysicalCoordinates g x a))) u).det| *
      Real.sqrt (realMetricFn g.form y
        (chartPt y (realExponentialMap g x (realPhysicalCoordinates g x u)))).det := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let e := realPhysicalCoordinates g x
  let v := e u
  let z := realExponentialMap g x v
  let F := fun a => chartPt y (realExponentialMap g x a)
  let D := fderiv ℝ (F ∘ e) u
  have hsrc : z ∈ (chartAt (ComplexVector n) y).source := hy
  have hz : chartPt y z ∈ chartTarget y :=
    (extChartAt (ComplexModel n) y).map_source
      (by simpa only [extChartAt_source] using hsrc)
  have hc : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartPt y) z :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hF : DifferentiableAt ℝ F v :=
    ((hc.comp v (realExponentialMap_contMDiff g x).contMDiffAt).contDiffAt.differentiableAt
      (by simp))
  have hD : D = (fderiv ℝ F v).comp e.toContinuousLinearMap :=
    (hF.hasFDerivAt.comp u e.toContinuousLinearEquiv.hasFDerivAt).fderiv
  have hDa (a : RIdx n) : D (realVec a) =
      realTangentCoords y z (realExponentialDifferential g x v
        (realInitialOrthonormalFrame g x (realFrameIndex n a))) := by
    rw [hD, ContinuousLinearMap.comp_apply]
    change fderiv ℝ F v (e (realVec a)) = _
    rw [realPhysicalCoordinates_realVec]
    exact (realExponentialDifferential_coords g x y v _ hsrc).symm
  have hG : (fun a b => realMetricInChart g.form y (chartPt y z)
      (realVec_basis n a) (realVec_basis n b)) = realMetricFn g.form y (chartPt y z) := by
    ext a b
    rw [realVec_basis_apply, realVec_basis_apply, realMetricInChart_basis g.form y _ hz]
  have hGram : Matrix.reindex (realFrameIndex n).symm (realFrameIndex n).symm
      (realExponentialGramMatrix g x v) =
      (LinearMap.toMatrix (realVec_basis n) (realVec_basis n) D.toLinearMap)ᵀ *
        realMetricFn g.form y (chartPt y z) *
        LinearMap.toMatrix (realVec_basis n) (realVec_basis n) D.toLinearMap := by
    rw [← hG, ← gram_matrix_comp]
    ext a b
    simp only [Matrix.reindex_apply, Equiv.symm_symm, realExponentialGramMatrix,
      realVec_basis_apply, hDa]
    exact (realMetricInChart_tangentCoords g.form y z hsrc _ _).symm
  have hdet := congrArg Matrix.det hGram
  rw [Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  change (realExponentialGramMatrix g x v).det =
    D.det * (realMetricFn g.form y (chartPt y z)).det * D.det at hdet
  change Real.sqrt (realExponentialGramMatrix g x v).det =
    |D.det| * Real.sqrt (realMetricFn g.form y (chartPt y z)).det
  rw [hdet, show D.det * (realMetricFn g.form y (chartPt y z)).det * D.det =
      D.det ^ 2 * (realMetricFn g.form y (chartPt y z)).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

set_option backward.isDefEq.respectTransparency false in
private theorem realExponential_measure_image_in_chart (g : SmoothMetric M)
    (x y : M.Carrier) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (s : Set (ComplexVector n)) (hs : MeasurableSet s)
    (hi : InjOn (realExponentialMap g x ∘ realPhysicalCoordinates g x) s)
    (hsource : (realExponentialMap g x ∘ realPhysicalCoordinates g x) '' s ⊆
      (chartAt (ComplexVector n) y).source) :
    μ ((realExponentialMap g x ∘ realPhysicalCoordinates g x) '' s) =
      ∫⁻ u in s, ENNReal.ofReal
        (realExponentialVolumeDensity g x (realPhysicalCoordinates g x u)) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let f := realExponentialMap g x ∘ realPhysicalCoordinates g x
  let F := fun a => chartPt y (f a)
  have hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 f :=
    (realExponentialMap_contMDiff g x).comp
      (realPhysicalCoordinates g x).toContinuousLinearMap.contMDiff
  have him : MeasurableSet (f '' s) :=
    hs.image_of_continuousOn_injOn hf.continuous.continuousOn hi
  have hsrc (u : ComplexVector n) (hu : u ∈ s) :
      f u ∈ (chartAt (ComplexVector n) y).source := hsource (mem_image_of_mem f hu)
  have hF (u : ComplexVector n) (hu : u ∈ s) : DifferentiableAt ℝ F u := by
    have hc : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
        (chartPt y) (f u) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc u hu)
    exact (hc.comp u hf.contMDiffAt).contDiffAt.differentiableAt (by simp)
  have hiF : InjOn F s := by
    intro u hu v hv huv
    apply hi hu hv
    exact (extChartAt (ComplexModel n) y).injOn
      (by simpa only [extChartAt_source] using hsrc u hu)
      (by simpa only [extChartAt_source] using hsrc v hv) huv
  change μ (f '' s) = _
  rw [hμ y (f '' s) him hsource, lebesgueC_eq_volume, ← image_comp]
  change ∫⁻ z in F '' s, ENNReal.ofReal (Real.sqrt (realMetricFn g.form y z).det) = _
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun u hu => (hF u hu).hasFDerivAt.hasFDerivWithinAt) hiF]
  apply setLIntegral_congr_fun hs
  intro u hu
  dsimp only
  rw [realExponentialVolumeDensity_in_chart g x y u (hsrc u hu),
    ENNReal.ofReal_mul (abs_nonneg _)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem realExponential_measure_image_coordinates (g : SmoothMetric M)
    (x : M.Carrier) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (s : Set (ComplexVector n)) (hs : MeasurableSet s)
    (hi : InjOn (realExponentialMap g x ∘ realPhysicalCoordinates g x) s) :
    μ ((realExponentialMap g x ∘ realPhysicalCoordinates g x) '' s) =
      ∫⁻ u in s, ENNReal.ofReal
        (realExponentialVolumeDensity g x (realPhysicalCoordinates g x u)) := by
  classical
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  let f := realExponentialMap g x ∘ realPhysicalCoordinates g x
  have hf : Continuous f := (realExponentialMap_contMDiff g x).continuous.comp
    (realPhysicalCoordinates g x).continuous
  obtain ⟨r, hr, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun y : M.Carrier => (chartAt (ComplexVector n) y).source)
    (fun y => (chartAt (ComplexVector n) y).open_source)
    (by intro z _; exact mem_iUnion.mpr ⟨z, mem_chart_source _ _⟩)
  have hrne : r.Nonempty := by
    obtain ⟨y, hyr, _⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨y, hyr⟩
  obtain ⟨c, hcr⟩ := hr.exists_eq_range hrne
  let U : ℕ → Set (ComplexVector n) := fun k =>
    f ⁻¹' (chartAt (ComplexVector n) (c k)).source
  have hUm (k : ℕ) : MeasurableSet (U k) :=
    ((chartAt (ComplexVector n) (c k)).open_source.preimage hf).measurableSet
  have hUc : (⋃ k, U k) = univ := by
    apply eq_univ_of_forall
    intro u
    obtain ⟨y, hyr, hy⟩ := mem_iUnion₂.mp (hcover (mem_univ (f u)))
    rw [hcr] at hyr
    obtain ⟨k, rfl⟩ := hyr
    exact mem_iUnion.mpr ⟨k, hy⟩
  let A : ℕ → Set (ComplexVector n) := fun k => s ∩ disjointed U k
  have hAm (k : ℕ) : MeasurableSet (A k) := hs.inter (MeasurableSet.disjointed hUm k)
  have hAs (k : ℕ) : A k ⊆ s := inter_subset_left
  have hAU (k : ℕ) : A k ⊆ U k := inter_subset_right.trans (disjointed_subset U k)
  have hAd : Pairwise (fun k l => Disjoint (A k) (A l)) :=
    (disjoint_disjointed U).mono fun k l hkl => hkl.mono inter_subset_right inter_subset_right
  have hAc : (⋃ k, A k) = s := by
    dsimp only [A]
    rw [← inter_iUnion, iUnion_disjointed, hUc, inter_univ]
  have him (k : ℕ) : MeasurableSet (f '' A k) :=
    (hAm k).image_of_continuousOn_injOn hf.continuousOn (hi.mono (hAs k))
  have hid : Pairwise (fun k l => Disjoint (f '' A k) (f '' A l)) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have heq : v = u := hi (hAs l hv) (hAs k hu) huv
    subst v
    exact disjoint_left.mp (hAd hkl) hu hv
  change μ (f '' s) = _
  rw [← hAc, image_iUnion, measure_iUnion hid him, lintegral_iUnion hAm hAd]
  apply tsum_congr
  intro k
  apply realExponential_measure_image_in_chart g x (c k) μ hμ (A k) (hAm k)
    (hi.mono (hAs k))
  rintro _ ⟨u, hu, rfl⟩
  exact hAU k hu

set_option backward.isDefEq.respectTransparency false in
/-- On every Borel set where the genuine exponential is injective, its
Riemannian image volume is the integral of its actual physical Gram density.
No nonsingularity assumption is required. -/
theorem realExponentialMap_image_volume (g : SmoothMetric M) (x : M.Carrier)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
    letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
    ∀ (s : Set (TangentSpace 𝓘(ℝ, ComplexVector n) x)), MeasurableSet s →
      InjOn (realExponentialMap g x) s →
      μ (realExponentialMap g x '' s) =
        ∫⁻ v in s, ENNReal.ofReal (realExponentialVolumeDensity g x v)
          ∂realTangentVolume g x := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  letI : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := borel _
  letI : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) x) := ⟨rfl⟩
  intro s hs hi
  let e := realPhysicalCoordinates g x
  have hse : MeasurableSet (e ⁻¹' s) := e.continuous.measurable hs
  have hie : InjOn (realExponentialMap g x ∘ e) (e ⁻¹' s) := by
    intro u hu v hv huv
    exact e.injective (hi hu hv huv)
  have h := realExponential_measure_image_coordinates g x μ hμ (e ⁻¹' s) hse hie
  rw [image_comp, e.surjective.image_preimage] at h
  rw [h]
  exact (realPhysicalCoordinates_measurePreserving g x).setLIntegral_comp_preimage_emb
    e.toHomeomorph.measurableEmbedding
    (fun v => ENNReal.ofReal (realExponentialVolumeDensity g x v)) s

end Yau.LeafProofs.L12Aux
