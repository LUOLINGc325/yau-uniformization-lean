import Yau.Proofs.B01ImageAlgebra

open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Set Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem imageFrameDomain_isOpen (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) : IsOpen (imageFrameDomain (r := r) E c a) :=
  c.isOpen_image_of_subset_source
    ((BundleDbar.localTriv (r := r) E a).open_baseSet.inter (chartAt (ComplexVector 1) a).open_source)
    (fun x _ => disc_mem_source c hc x)

theorem imageFrameDomain_subset (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) : imageFrameDomain (r := r) E c a ⊆ puncturedUnitDisc := by
  rintro z ⟨x, _, rfl⟩
  exact disc_mem c hc x

theorem imageFrameDomain_self (c : DiscCoordinate M) (a : M.Carrier) :
    c a ∈ imageFrameDomain (r := r) E c a :=
  ⟨a, ⟨mem_baseSet_trivializationAt (ComplexVector r) E a,
    mem_chart_source (ComplexVector 1) a⟩, rfl⟩

theorem imageFrameDomain_symm_mem (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ℂ} (hz : z ∈ imageFrameDomain (r := r) E c a) :
    c.symm z ∈ (BundleDbar.localTriv (r := r) E a).baseSet ∧
      c.symm z ∈ (chartAt (ComplexVector 1) a).source := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [disc_left_inv c hc]
  exact ⟨hx.1, hx.2⟩

theorem baseChange_mem_localDomain (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ℂ} (hz : z ∈ imageFrameDomain (r := r) E c a) :
    baseChange c a z ∈ BundleDbar.localDomain (r := r) E a := by
  have hm := imageFrameDomain_symm_mem E c hc a hz
  refine ⟨(extChartAt (ComplexModel 1) a).map_source (by simpa only [extChartAt_source] using hm.2), ?_⟩
  simpa only [mem_preimage, chartInv_baseChange E c hc a hz] using hm.1

theorem baseChange_contDiffAt (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ℂ} (hz : z ∈ imageFrameDomain (r := r) E c a) :
    ContDiffAt ℂ ∞ (baseChange c a) z := by
  have hi : ContMDiffAt 𝓘(ℂ, ℂ) (ComplexModel 1) ⊤ c.symm z :=
    hc.2.2.2.contMDiffAt (puncturedUnitDisc_isOpen.mem_nhds
      (imageFrameDomain_subset E c hc a hz))
  have ho : ContMDiffAt (ComplexModel 1) (ComplexModel 1) ⊤ (chartPt a) (c.symm z) :=
    contMDiffAt_extChartAt' (imageFrameDomain_symm_mem E c hc a hz).2
  exact ((ho.comp z hi).of_le le_top).contDiffAt

theorem imageFrame_eq_mapCoefficients (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (A : MapToTrivial E q) (a : M.Carrier) {z : ℂ}
    (hz : z ∈ imageFrameDomain (r := r) E c a) :
    imageFrame (r := r) E c A a z =
      mapCoefficients (r := r) E A a (baseChange c a z) := by
  unfold imageFrame mapCoefficients
  rw [chartInv_baseChange E c hc a hz]

theorem imageFrame_linearMap (c : DiscCoordinate M) (A : MapToTrivial E q)
    (a : M.Carrier) (z : ℂ) :
    frameLinear (imageFrame (r := r) E c A a z) =
      (A (c.symm z)).toLinearMap.comp
        ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z)).toLinearMap := by
  apply (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.ext
  intro i
  simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, stdVec] using imageFrame_stdVec E c A a z i

theorem imageFrame_range (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (A : MapToTrivial E q) (a : M.Carrier) {z : ℂ}
    (hz : z ∈ imageFrameDomain (r := r) E c a) :
    LinearMap.range (frameLinear (imageFrame (r := r) E c A a z)) = imageFibers E c A z := by
  rw [imageFrame_linearMap]
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro v ⟨u, rfl⟩
    refine ⟨(BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (c.symm z) u, ?_⟩
    change A (c.symm z) ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z)
      ((BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (c.symm z) u)) = _
    rw [Trivialization.symmL_continuousLinearMapAt _ (imageFrameDomain_symm_mem E c hc a hz).1]
    rfl

theorem imageFrame_injective (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (a : M.Carrier) {z : ℂ}
    (hz : z ∈ imageFrameDomain (r := r) E c a) :
    Function.Injective (frameLinear (imageFrame (r := r) E c A a z)) := by
  rw [imageFrame_linearMap]
  intro u v huv
  have hs := hA (c.symm z) huv
  have ht := congrArg ((BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (c.symm z)) hs
  change (BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (c.symm z)
      ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z) u) =
    (BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (c.symm z)
      ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z) v) at ht
  rwa [Trivialization.continuousLinearMapAt_symmL _ (imageFrameDomain_symm_mem E c hc a hz).1,
    Trivialization.continuousLinearMapAt_symmL _ (imageFrameDomain_symm_mem E c hc a hz).1] at ht

theorem imageFrame_differentiableOn (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (A : MapToTrivial E q) (hA : HolomorphicMap (r := r) E A) (a : M.Carrier) :
    DifferentiableOn ℂ (imageFrame (r := r) E c A a) (imageFrameDomain (r := r) E c a) := by
  have ht : DifferentiableOn ℂ (baseChange c a) (imageFrameDomain (r := r) E c a) :=
    fun z hz => ((baseChange_contDiffAt E c hc a hz).differentiableAt (by simp)).differentiableWithinAt
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  have hentry := (differentiableOn_pi.mp (differentiableOn_pi.mp (hA a) i) j)
  have hcomp := hentry.comp ht (fun z hz => baseChange_mem_localDomain E c hc a hz)
  exact hcomp.congr (fun z hz => congrFun (congrFun (imageFrame_eq_mapCoefficients E c hc A a hz) i) j)

theorem imageLocalFrameTransport : ImageLocalFrameTransport (r := r) (q := q) E := by
  intro c hc A _ hA hI
  have hf : ∀ a, LocalEmbeddedFrame (imageFibers E c A)
      (imageFrame (r := r) E c A a) (imageFrameDomain (r := r) E c a) := by
    intro a
    exact ⟨imageFrameDomain_isOpen E c hc a, imageFrameDomain_subset E c hc a,
      imageFrame_differentiableOn E c hc A hA a,
      fun z hz => ⟨imageFrame_range E c hc A a hz, imageFrame_injective E c hc A hI a hz⟩⟩
  refine ⟨hf, ?_⟩
  intro z hz
  refine ⟨imageFrameDomain (r := r) E c (c.symm z), ?_,
    imageFrame (r := r) E c A (c.symm z), hf (c.symm z)⟩
  simpa only [disc_right_inv c hc hz] using imageFrameDomain_self E c (c.symm z)

theorem imageSection_local (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (A : MapToTrivial E q) (s : Section E) (a : M.Carrier) {z : ℂ}
    (hz : z ∈ imageFrameDomain (r := r) E c a) :
    imageSection E c A s z = frameLinear (imageFrame (r := r) E c A a z)
      (sectionCoefficients (r := r) E s a (baseChange c a z)) := by
  rw [imageFrame_linearMap]
  unfold sectionCoefficients
  rw [chartInv_baseChange E c hc a hz]
  change A (c.symm z) (s (c.symm z)) =
    A (c.symm z) ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z)
      ((BundleDbar.localTriv (r := r) E a).continuousLinearMapAt ℂ (c.symm z) (s (c.symm z))))
  rw [Trivialization.symmL_continuousLinearMapAt _ (imageFrameDomain_symm_mem E c hc a hz).1]

theorem imageSection_local_differentiableOn (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (A : MapToTrivial E q) (hA : HolomorphicMap (r := r) E A)
    (s : Section E) (hs : HolomorphicSection (r := r) E s) (a : M.Carrier) :
    DifferentiableOn ℂ (imageSection E c A s) (imageFrameDomain (r := r) E c a) := by
  have ht : DifferentiableOn ℂ (baseChange c a) (imageFrameDomain (r := r) E c a) :=
    fun z hz => ((baseChange_contDiffAt E c hc a hz).differentiableAt (by simp)).differentiableWithinAt
  have hS := (hs a).comp ht (fun z hz => baseChange_mem_localDomain E c hc a hz)
  have hF := imageFrame_differentiableOn E c hc A hA a
  have hmul : DifferentiableOn ℂ (fun z => frameLinear (imageFrame (r := r) E c A a z)
      (sectionCoefficients (r := r) E s a (baseChange c a z)))
      (imageFrameDomain (r := r) E c a) := by
    apply (differentiableOn_piLp 2).mpr
    intro i
    change DifferentiableOn ℂ (fun z => ∑ j, imageFrame (r := r) E c A a z i j *
      sectionCoefficients (r := r) E s a (baseChange c a z) j) _
    intro z hz
    exact DifferentiableWithinAt.fun_sum (fun j _ =>
      ((differentiableOn_pi.mp (differentiableOn_pi.mp hF i) j) z hz).mul
        ((differentiableOn_piLp 2).mp hS j z hz))
  exact hmul.congr (fun z hz => imageSection_local E c hc A s a hz)

theorem imageSectionTransport : ImageSectionTransport (r := r) (q := q) E := by
  intro c hc A _ hA s hs
  refine ⟨?_, fun z _ => imageSection_mem E c A s z⟩
  intro z hz
  have hm : z ∈ imageFrameDomain (r := r) E c (c.symm z) := by
    simpa only [disc_right_inv c hc hz] using imageFrameDomain_self E c (c.symm z)
  exact ((imageSection_local_differentiableOn E c hc A hA s hs (c.symm z)).differentiableAt
    ((imageFrameDomain_isOpen E c hc (c.symm z)).mem_nhds hm)).differentiableWithinAt

end Yau.Proofs.B01Aux
