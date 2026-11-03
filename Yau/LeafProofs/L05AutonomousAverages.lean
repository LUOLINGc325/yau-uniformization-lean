import Yau.LeafProofs.L05AutonomousProbability
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UrysohnsLemma

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A norm-preserving topological extension with a genuine compact cutoff. This
introduces no derivatives or PDE outside the compact set. -/
theorem auto_compact_extension {n : ℕ} {K : Set (Point n)} (hK : IsCompact K)
    {u : Point n → ℝ} (hu : ContinuousOn u K) :
    ∃ w : Point n →ᵇ ℝ, EqOn w u K ∧ UniformContinuous (w : Point n → ℝ) ∧
      HasCompactSupport (w : Point n → ℝ) ∧
      ∀ M : ℝ, 0≤M → (∀ p∈K, |u p|≤M) → ‖w‖≤M := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun p => u p,(continuousOn_iff_continuous_domRestrict.mp hu)⟩
  obtain ⟨v,hvnorm,hveq⟩ := f.exists_norm_eq_domRestrict_eq_of_closed hK.isClosed
  obtain ⟨eta,hetaK,hetaEmpty,hetaCompact,hetaRange⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let etaB : Point n →ᵇ ℝ := BoundedContinuousFunction.mkOfBound eta 2 (by
    intro p q
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith only [(hetaRange p).1,(hetaRange q).2],
      by linarith only [(hetaRange p).2,(hetaRange q).1]⟩)
  have hetaNorm : ‖etaB‖≤1 := (BoundedContinuousFunction.norm_le (by norm_num)).mpr (by
    intro p
    change ‖eta p‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (hetaRange p).1]
    exact (hetaRange p).2)
  let w : Point n →ᵇ ℝ := etaB*v
  have hwNorm : ‖w‖≤‖f‖ := by
    calc
      ‖w‖ ≤ ‖etaB‖*‖v‖ := norm_mul_le _ _
      _ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right hetaNorm (norm_nonneg _)
      _ = ‖f‖ := by rw [one_mul,hvnorm]
  have hwCompact : HasCompactSupport (w : Point n → ℝ) := by
    exact hetaCompact.mul_right
  refine ⟨w,?_,w.continuous.uniformContinuous_of_tendsto_cocompact hwCompact.is_zero_at_infty,
    hwCompact,?_⟩
  · intro p hp
    have hval := congrArg (fun q : K →ᵇ ℝ => q ⟨p,hp⟩) hveq
    change v p=u p at hval
    change eta p*v p=u p
    have he := hetaK hp
    change eta p=1 at he
    rw [he,one_mul,hval]
  intro M hM hbound
  apply hwNorm.trans
  apply (BoundedContinuousFunction.norm_le hM).mpr
  intro p
  change ‖u p.val‖≤M
  simpa only [Real.norm_eq_abs] using hbound p.val p.property

def autoSpatialTranslateBCF {n : ℕ} (w : Point n →ᵇ ℝ) (y : Space n) : Point n →ᵇ ℝ :=
  w.compContinuous ⟨fun p => p+(y,0),(continuous_id.add_const ((y,0) : Point n))⟩

theorem autoSpatialTranslateBCF_apply {n : ℕ} (w : Point n →ᵇ ℝ) (y : Space n) (p : Point n) :
    autoSpatialTranslateBCF w y p=w (p+(y,0)) := rfl

theorem autoSpatialTranslateBCF_norm {n : ℕ} (w : Point n →ᵇ ℝ) (y : Space n) :
    ‖autoSpatialTranslateBCF w y‖≤‖w‖ := BoundedContinuousFunction.norm_compContinuous_le _ _

/-- The parameter map is continuous in the actual supremum norm, not merely pointwise. -/
theorem autoSpatialTranslateBCF_uniformContinuous {n : ℕ} (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) : UniformContinuous (autoSpatialTranslateBCF w) := by
  apply Metric.uniformContinuous_iff.mpr
  intro eps heps
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuous_iff.mp hw (eps/2) (by positivity)
  refine ⟨delta,hdelta,?_⟩
  intro y z hyz
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity : 0≤eps/2)).mpr ?_)
    (by linarith only [heps] : eps/2<eps)
  intro p
  change dist (w (p+(y,0))) (w (p+(z,0)))≤eps/2
  apply le_of_lt (hclose ?_)
  simpa only [dist_add_left,Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hyz

/-- Continuity and actual integrability on a closed target, including its terminal face.
Only containment in the original CLOSED source cylinder is required here. -/
theorem auto_probability_spatial_average_continuous {n : ℕ} {S : Set (Point n)}
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (K : Set (Space n)) (hK : IsCompact K) (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hmu : ∀ᵐ y ∂μ, y∈K)
    (hbuffer : ∀ y∈K, ∀ p∈S, p+(y,0)∈unitClosed n) :
    (∀ p∈S, Integrable (fun y => u (p.1+y,p.2)) μ) ∧
      ContinuousOn (fun p => ∫ y, u (p.1+y,p.2) ∂μ) S := by
  classical
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  obtain ⟨w,hwu,hwUniform,hwCompact,hwBound⟩ := auto_compact_extension hD hu
  obtain ⟨y0,hy0⟩ := hmu.exists
  let g : Space n → (Point n →ᵇ ℝ) := K.piecewise (autoSpatialTranslateBCF w)
    (fun _ => autoSpatialTranslateBCF w y0)
  have hg : StronglyMeasurable g := StronglyMeasurable.piecewise hK.isClosed.measurableSet
    (autoSpatialTranslateBCF_uniformContinuous w hwUniform).continuous.stronglyMeasurable
    stronglyMeasurable_const
  have hgbound (y : Space n) : ‖g y‖≤‖w‖ := by
    by_cases hy : y∈K
    · simpa only [g,Set.piecewise_eq_of_mem K _ _ hy] using autoSpatialTranslateBCF_norm w y
    simpa only [g,Set.piecewise_eq_of_notMem K _ _ hy] using autoSpatialTranslateBCF_norm w y0
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable ‖w‖ (ae_of_all μ hgbound)
  have hpointEq (p : Point n) (hp : p∈S) :
      (fun y => u (p.1+y,p.2)) =ᵐ[μ] (fun y => g y p) := by
    filter_upwards [hmu] with y hy
    simp only [g,Set.piecewise_eq_of_mem K _ _ hy,autoSpatialTranslateBCF_apply]
    have hh := hwu (hbuffer y hy p hp)
    have hpoint : p+(y,0)=(p.1+y,p.2) := by
      rcases p with ⟨x,t⟩
      simp only [Prod.mk_add_mk,add_zero]
    rw [hpoint] at hh ⊢
    exact hh.symm
  have heq : EqOn (fun p => ∫ y, u (p.1+y,p.2) ∂μ) (fun p => (∫ y, g y ∂μ) p) S := by
    intro p hp
    change (∫ y, u (p.1+y,p.2) ∂μ)=(∫ y, g y ∂μ) p
    rw [auto_bcf_integral_apply hgi p]
    exact integral_congr_ae (hpointEq p hp)
  refine ⟨fun p hp => ((BoundedContinuousFunction.evalCLM ℝ p).integrable_comp hgi).congr
    (hpointEq p hp).symm,?_⟩
  exact (∫ y, g y ∂μ).continuous.continuousOn.congr heq

/-- Actual compactly supported probability averages of allowed spatial translates.
The measure is a Borel probability measure on Space n; all PDE assertions are
transported from unitOpen and no regularity of u is assumed. -/
theorem auto_probability_spatial_average {n : ℕ} {Q : Set (Point n)}
    {ell L : ℝ} {F : Sym n → ℝ} (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L)
    (hF : Continuous F) (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsub : viscositySub (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (K : Set (Space n)) (hK : IsCompact K) (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hmu : ∀ᵐ y ∂μ, y∈K)
    (hbuffer : ∀ y∈K, ∀ p∈Q, p+(y,0)∈unitOpen n) :
    (∀ p∈Q, Integrable (fun y => u (p.1+y,p.2)) μ) ∧
    ContinuousOn (fun p => ∫ y, u (p.1+y,p.2) ∂μ) Q ∧
      viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => ∫ y, u (p.1+y,p.2) ∂μ) := by
  classical
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  obtain ⟨w,hwu,hwUniform,hwCompact,hwBound⟩ := auto_compact_extension hD hu
  obtain ⟨y0,hy0⟩ := hmu.exists
  let g : Space n → (Point n →ᵇ ℝ) := K.piecewise (autoSpatialTranslateBCF w)
    (fun _ => autoSpatialTranslateBCF w y0)
  have hg : StronglyMeasurable g := StronglyMeasurable.piecewise hK.isClosed.measurableSet
    (autoSpatialTranslateBCF_uniformContinuous w hwUniform).continuous.stronglyMeasurable
    stronglyMeasurable_const
  have hgbound (y : Space n) : ‖g y‖≤‖w‖ := by
    by_cases hy : y∈K
    · simpa only [g,Set.piecewise_eq_of_mem K _ _ hy] using autoSpatialTranslateBCF_norm w y
    simpa only [g,Set.piecewise_eq_of_notMem K _ _ hy] using autoSpatialTranslateBCF_norm w y0
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable ‖w‖ (ae_of_all μ hgbound)
  have hsubw (y : Space n) (hy : y∈K) :
      viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => autoSpatialTranslateBCF w y p) := by
    apply viscositySub_eqOn_open hQ _ (auto_translate_sub hsub (y,0) (hbuffer y hy))
    intro p hp
    exact hwu (unitOpen_subset_unitClosed (hbuffer y hy p hp))
  have hsubg (y : Space n) : viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => g y p) := by
    by_cases hy : y∈K
    · simpa only [g,Set.piecewise_eq_of_mem K _ _ hy] using hsubw y hy
    simpa only [g,Set.piecewise_eq_of_notMem K _ _ hy] using hsubw y0 hy0
  have havg := auto_bcf_probability_sub hQ hell hL hF hE hC μ g hg hgi hsubg
  have hpointEq (p : Point n) (hp : p∈Q) :
      (fun y => u (p.1+y,p.2)) =ᵐ[μ] (fun y => g y p) := by
    filter_upwards [hmu] with y hy
    simp only [g,Set.piecewise_eq_of_mem K _ _ hy,autoSpatialTranslateBCF_apply]
    have hh := hwu (unitOpen_subset_unitClosed (hbuffer y hy p hp))
    have hpoint : p+(y,0)=(p.1+y,p.2) := by
      rcases p with ⟨x,t⟩
      simp only [Prod.mk_add_mk,add_zero]
    rw [hpoint] at hh ⊢
    exact hh.symm
  have heq : EqOn (fun p => ∫ y, u (p.1+y,p.2) ∂μ) (fun p => ∫ y, g y p ∂μ) Q :=
    fun p hp => integral_congr_ae (hpointEq p hp)
  have hcont : ContinuousOn (fun p => ∫ y, g y p ∂μ) Q := by
    have heq' : (fun p => ∫ y, g y p ∂μ)=(fun p => (∫ y, g y ∂μ) p) := by
      funext p
      exact (auto_bcf_integral_apply hgi p).symm
    rw [heq']
    exact (∫ y, g y ∂μ).continuous.continuousOn
  have hactualInt (p : Point n) (hp : p∈Q) : Integrable (fun y => u (p.1+y,p.2)) μ :=
    ((BoundedContinuousFunction.evalCLM ℝ p).integrable_comp hgi).congr (hpointEq p hp).symm
  exact ⟨hactualInt,hcont.congr (fun p hp => heq hp),viscositySub_eqOn_open hQ heq havg⟩

theorem auto_probability_spatial_average_sub {n : ℕ} {Q : Set (Point n)}
    {ell L : ℝ} {F : Sym n → ℝ} (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L)
    (hF : Continuous F) (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsub : viscositySub (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (K : Set (Space n)) (hK : IsCompact K) (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hmu : ∀ᵐ y ∂μ, y∈K)
    (hbuffer : ∀ y∈K, ∀ p∈Q, p+(y,0)∈unitOpen n) :
    ContinuousOn (fun p => ∫ y, u (p.1+y,p.2) ∂μ) Q ∧
      viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => ∫ y, u (p.1+y,p.2) ∂μ) :=
  (auto_probability_spatial_average hQ hell hL hF hE hC hu hsub K hK μ hmu hbuffer).2

end Yau.LeafProofs.L05AutonomousAux
