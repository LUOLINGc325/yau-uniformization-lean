import Yau.Proofs.B01Coordinate

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

theorem imageEquiv_coe (c : DiscCoordinate M) (A : MapToTrivial E q)
    (hA : PointwiseInjective E A) (z : ℂ) (u : E (c.symm z)) :
    (imageEquiv E c A hA z u : ComplexVector q) = A (c.symm z) u := rfl

theorem imageEquiv_symm_map (c : DiscCoordinate M) (A : MapToTrivial E q)
    (hA : PointwiseInjective E A) (z : ℂ) (u : imageFibers E c A z) :
    A (c.symm z) ((imageEquiv E c A hA z).symm u) = u.1 := by
  exact congrArg Subtype.val ((imageEquiv E c A hA z).apply_symm_apply u)

theorem imageMetric_apply (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (z : ℂ)
    (u v : E (c.symm z)) :
    (imageMetric E c k A hA z).toFun
      (imageEquiv E c A hA z u) (imageEquiv E c A hA z v) =
        (k (c.symm z)).toFun u v := by
  simp only [imageMetric, transportMetric, LinearEquiv.symm_apply_apply]

theorem imageNormSq_symm (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (z : ℂ)
    (u : imageFibers E c A z) :
    hermitianNormSq (imageMetric E c k A hA z) u =
      hermitianNormSq (k (c.symm z)) ((imageEquiv E c A hA z).symm u) := rfl

theorem imageBoundTransport : ImageBoundTransport (q := q) E := by
  intro c k A hA C hbound z _ u
  simpa only [imageEquiv_symm_map, imageNormSq_symm] using
    hbound (c.symm z) ((imageEquiv E c A hA z).symm u)

theorem imageSection_mem (c : DiscCoordinate M) (A : MapToTrivial E q)
    (s : Section E) (z : ℂ) : imageSection E c A s z ∈ imageFibers E c A z :=
  ⟨s (c.symm z), rfl⟩

theorem imageSection_eq_imageEquiv (c : DiscCoordinate M) (A : MapToTrivial E q)
    (hA : PointwiseInjective E A) (s : Section E) (z : ℂ) :
    (⟨imageSection E c A s z, imageSection_mem E c A s z⟩ : imageFibers E c A z) =
      imageEquiv E c A hA z (s (c.symm z)) := rfl

theorem embeddedNormSq_imageSection (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (hA : PointwiseInjective E A) (s : Section E) (z : ℂ) :
    embeddedNormSq (imageFibers E c A) (imageMetric E c k A hA)
      (imageSection E c A s) z = hermitianNormSq (k (c.symm z)) (s (c.symm z)) := by
  classical
  simp only [embeddedNormSq, dite_eq_left (imageSection_mem E c A s z)]
  rw [imageSection_eq_imageEquiv E c A hA s z]
  exact congrArg Complex.re (imageMetric_apply E c k A hA z _ _)

theorem imageFrame_stdVec (c : DiscCoordinate M) (A : MapToTrivial E q)
    (a : M.Carrier) (z : ℂ) (j : Fin r) :
    frameLinear (imageFrame (r := r) E c A a z) (stdVec j) =
      A (c.symm z) ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z) (stdVec j)) := by
  ext i
  simp [frameLinear, Matrix.toLpLin_apply, imageFrame, stdVec]

theorem imageFrameLift_eq (c : DiscCoordinate M) (A : MapToTrivial E q)
    (hA : PointwiseInjective E A) (a : M.Carrier) (z : ℂ) (j : Fin r) :
    frameLift (imageFibers E c A) (imageFrame (r := r) E c A a) z j =
      imageEquiv E c A hA z
        ((BundleDbar.localTriv (r := r) E a).symmL ℂ (c.symm z) (stdVec j)) := by
  classical
  have hm : frameLinear (imageFrame (r := r) E c A a z) (stdVec j) ∈ imageFibers E c A z := by
    rw [imageFrame_stdVec E c A a z j]
    exact ⟨_, rfl⟩
  apply Subtype.ext
  unfold frameLift
  rw [dite_eq_left hm]
  exact imageFrame_stdVec E c A a z j

theorem chartInv_baseChange (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) {z : ℂ} (hz : z ∈ imageFrameDomain (r := r) E c a) :
    chartInv a (baseChange c a z) = c.symm z := by
  obtain ⟨x, hx, rfl⟩ := hz
  simp only [baseChange, disc_left_inv c hc]
  exact (extChartAt (ComplexModel 1) a).left_inv (by simpa only [extChartAt_source] using hx.2)

theorem imageMetricTransport : ImageMetricTransport (r := r) (q := q) E := by
  intro c hc k A hA
  refine ⟨imageMetric_apply E c k A hA, ?_⟩
  intro a z hz
  ext i j
  change (imageMetric E c k A hA z).toFun
    (frameLift (imageFibers E c A) (imageFrame (r := r) E c A a) z i)
    (frameLift (imageFibers E c A) (imageFrame (r := r) E c A a) z j) = _
  rw [imageFrameLift_eq E c A hA a z i, imageFrameLift_eq E c A hA a z j,
    imageMetric_apply]
  dsimp only [BundleDbar.metricMatrix]
  rw [chartInv_baseChange E c hc a hz]

theorem imageIntegralTransport : ImageIntegralTransport (r := r) (q := q) E := by
  intro c hc k A hA _ _ _ s _
  refine ⟨?_, ?_⟩
  · unfold sectionIntegral
    rw [lintegral_discArea c hc]
    simp only [embeddedNormSq_imageSection]
  · intro ρ σ _ hρ
    let S : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < ρ}
    have hS : MeasurableSet S :=
      ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).measurableSet
    have hSD : S ⊆ puncturedUnitDisc := fun z hz => ⟨hz.1, hz.2.trans hρ⟩
    change (∫⁻ x in c ⁻¹' S, ENNReal.ofReal
      (hermitianNormSq (k x) (s x) * ‖c x‖ ^ (-σ)) ∂BundlePresentation.discArea c) = _
    rw [setLIntegral_discArea c hc S hS hSD]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [embeddedNormSq_imageSection, disc_right_inv c hc (hSD hz)]

end Yau.Proofs.B01Aux
