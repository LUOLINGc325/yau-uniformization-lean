import Yau.LeafProofs.L12JacobiRegularity
import Yau.LeafProofs.L12HopfRinow

/-! Actual two-endpoint local geodesic branches. The vertical derivative
is the genuine Jacobi differential; its invertible triangular coordinate
derivative supplies the branch by the C1 inverse function theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- Actual start/end pair of a complete geodesic segment. -/
def realGeodesicEndpointMap (g : SmoothMetric M) (d : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : M.Carrier × M.Carrier :=
  (q.proj, (realGeodesicFlow g q d).proj)

theorem realGeodesicEndpointMap_contMDiff (g : SmoothMetric M) (d : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1
      (realGeodesicEndpointMap g d) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have hflow := (realGeodesicFlow_joint_contMDiff g).comp
    (contMDiff_id.prodMk (contMDiff_const (c := d)))
  have hproj : ContMDiff (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1
      (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => p.proj) :=
    (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).of_le (by simp)
  exact hproj.prodMk (hproj.comp hflow)

def realGeodesicEndpointChartMap (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ) :
    ComplexVector n × ComplexVector n → ComplexVector n × ComplexVector n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact extChartAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (realGeodesicEndpointMap g d q) ∘ realGeodesicEndpointMap g d ∘
        (extChartAt (realPhaseModel n) q).symm

theorem realGeodesicEndpointChartMap_contDiffAt (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContDiffAt ℝ 1 (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  have h := (contMDiffAt_iff.mp (realGeodesicEndpointMap_contMDiff g d q)).2
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h

theorem realGeodesicEndpointChartMap_fst_eventually (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    (fun z => (realGeodesicEndpointChartMap g q d z).1) =ᶠ[𝓝 (extChartAt (realPhaseModel n) q q)] Prod.fst := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  filter_upwards [(isOpen_extChartAt_target (I := realPhaseModel n) q).mem_nhds
    (mem_extChartAt_target q)] with z hz
  have hz' := (realPhaseChart_target q z).mp hz
  change chartPt q.proj (((extChartAt (realPhaseModel n) q).symm z).proj) = z.1
  rw [realPhasePoint_eq_extChartAt_symm q z hz']
  exact (extChartAt (ComplexModel n) q.proj).right_inv hz'

theorem realGeodesicEndpointChartMap_fderiv_fst (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ) (a : ComplexVector n × ComplexVector n) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    (fderiv ℝ (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q) a).1 = a.1 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have hF := (realGeodesicEndpointChartMap_contDiffAt g q d).differentiableAt (by simp)
  have hfirst : HasFDerivAt (fun z => (realGeodesicEndpointChartMap g q d z).1)
      (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)) (extChartAt (realPhaseModel n) q q) :=
    (realGeodesicEndpointChartMap_fst_eventually g q d).hasFDerivAt_iff.mpr
      (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt
  have hcomp := (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp
    (extChartAt (realPhaseModel n) q q) hF.hasFDerivAt
  exact congrArg (fun L : ComplexVector n × ComplexVector n →L[ℝ] ComplexVector n => L a)
    (hcomp.unique hfirst)

theorem realGeodesicEndpointChartMap_fderiv_vertical (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) q.proj) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    (fderiv ℝ (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q)
      (0, realTangentCoords q.proj q.proj w)).2 =
        realTangentCoords (realGeodesicFlow g q d).proj (realGeodesicFlow g q d).proj
          (realGeodesicJacobiField g q w d) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form q.proj
  letI := underlyingRealTangentInnerProductSpace g.form q.proj
  let F := realGeodesicEndpointChartMap g q d
  let U := realVelocityPhaseCoordinates g q 0
  let z := extChartAt (realPhaseModel n) q q
  let y := (realGeodesicFlow g q d).proj
  have hU (a : TangentSpace 𝓘(ℝ, ComplexVector n) q.proj) : U a =
      extChartAt (realPhaseModel n) q
        (⟨q.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := by
    dsimp only [U, realVelocityPhaseCoordinates]
    rw [realGeodesicFlow_zero, realGeodesicFlow_zero]
  have hU₀ : U q.2 = z := hU q.2
  have hFD := (realGeodesicEndpointChartMap_contDiffAt g q d).differentiableAt (by simp)
  have hUD := (realVelocityPhaseCoordinates_contDiffAt g q 0).differentiableAt (by simp)
  have hFD' : HasFDerivAt F (fderiv ℝ F z) (U q.2) := by rw [hU₀]; exact hFD.hasFDerivAt
  have hcomp := hFD'.comp q.2 hUD.hasFDerivAt
  have hsnd := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp q.2 hcomp
  have hN : ∀ᶠ a : TangentSpace 𝓘(ℝ, ComplexVector n) q.proj in 𝓝 q.2,
      (⟨q.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) ∈
        (extChartAt (realPhaseModel n) q).source :=
    (realTangentFiber_contMDiff g q.proj).continuous.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realPhaseModel n) q)
  have heq : (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) q.proj => (F (U a)).2) =ᶠ[𝓝 q.2]
      (fun a => chartPt y (realVelocityBaseFlow g q.proj a d)) := by
    filter_upwards [hN] with a ha
    dsimp only [F, realGeodesicEndpointChartMap, Function.comp_apply]
    rw [hU a, (extChartAt (realPhaseModel n) q).left_inv ha]
    rfl
  have hactual := heq.hasFDerivAt_iff.mp hsnd
  have hcoords := realGeodesicJacobiField_in_chart g q w d y (mem_chart_source _ _)
  rw [hactual.fderiv] at hcoords
  simp only [ContinuousLinearMap.comp_apply] at hcoords
  change realTangentCoords y y (realGeodesicJacobiField g q w d) =
    (fderiv ℝ F z (fderiv ℝ U q.2 w)).2 at hcoords
  dsimp only [U] at hcoords
  rw [realVelocityPhaseCoordinates_zero_fderiv_apply g q w] at hcoords
  exact hcoords.symm

theorem realGeodesicEndpointChartMap_fderiv_injective (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (hdet : (realGeodesicJacobiMatrix g q d).det ≠ 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    Function.Injective (fderiv ℝ (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let D := fderiv ℝ (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q)
  let y := (realGeodesicFlow g q d).proj
  have hker (a : ComplexVector n × ComplexVector n) (ha : D a = 0) : a = 0 := by
    have ha₁ : a.1 = 0 := by
      have h := congrArg Prod.fst ha
      rw [realGeodesicEndpointChartMap_fderiv_fst] at h
      exact h
    have hae : a = (0, a.2) := Prod.ext ha₁ rfl
    let w := realFrameCLM q.proj q.proj a.2
    have hVert := realGeodesicEndpointChartMap_fderiv_vertical g q d w
    rw [realTangentCoords_realFrameCLM q.proj q.proj (mem_chart_source _ _)] at hVert
    have hcoords : realTangentCoords y y (realGeodesicJacobiField g q w d) = 0 := by
      rw [← hVert, ← hae]
      change (D a).2 = 0
      rw [ha]
      rfl
    have hJ := congrArg (realFrameCLM y y) hcoords
    rw [realFrameCLM_realTangentCoords y y (mem_chart_source _ _), map_zero] at hJ
    have hw : w = 0 := by
      apply realGeodesicJacobiOperator_injective_of_det_ne_zero g q d hdet
      rw [realGeodesicJacobiOperator_apply, hJ, map_zero]
    have ha₂ : a.2 = 0 := by
      have h := congrArg (realTangentCoords q.proj q.proj) hw
      rw [realTangentCoords_realFrameCLM q.proj q.proj (mem_chart_source _ _), map_zero] at h
      exact h
    exact Prod.ext ha₁ ha₂
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hab, sub_self]

/-- The true endpoint-pair derivative is invertible by its triangular
structure and the genuine vertical Jacobi differential. -/
def realGeodesicEndpointChartEquiv (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (hdet : (realGeodesicJacobiMatrix g q d).det ≠ 0) :
    (ComplexVector n × ComplexVector n) ≃L[ℝ] (ComplexVector n × ComplexVector n) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let D := fderiv ℝ (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q)
  have hi := realGeodesicEndpointChartMap_fderiv_injective g q d hdet
  exact (LinearEquiv.ofBijective D.toLinearMap ⟨hi, LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv

theorem realGeodesicEndpointChartMap_hasFDerivAt_equiv (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (hdet : (realGeodesicJacobiMatrix g q d).det ≠ 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    HasFDerivAt (realGeodesicEndpointChartMap g q d)
      (realGeodesicEndpointChartEquiv g q d hdet).toContinuousLinearMap
      (extChartAt (realPhaseModel n) q q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have h := (realGeodesicEndpointChartMap_contDiffAt g q d).differentiableAt (by simp)
  have he : (realGeodesicEndpointChartEquiv g q d hdet).toContinuousLinearMap =
      fderiv ℝ (realGeodesicEndpointChartMap g q d) (extChartAt (realPhaseModel n) q q) := by
    apply ContinuousLinearMap.ext
    intro a
    rfl
  rw [he]
  exact h.hasFDerivAt

/-- A nonsingular actual Jacobi differential gives a genuine C1 local
branch of complete geodesics with both endpoints prescribed. -/
theorem exists_realGeodesic_endpointBranch (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (hdet : (realGeodesicJacobiMatrix g q d).det ≠ 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ U : Set (M.Carrier × M.Carrier), IsOpen U ∧ realGeodesicEndpointMap g d q ∈ U ∧
      ∃ P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
        ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U ∧
        P (realGeodesicEndpointMap g d q) = q ∧
        (∀ z ∈ U, (P z).proj = z.1 ∧ (realGeodesicFlow g (P z) d).proj = z.2) ∧
        (∀ᶠ q' in 𝓝 q, P (realGeodesicEndpointMap g d q') = q') := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  let F := realGeodesicEndpointChartMap g q d
  let z₀ := extChartAt (realPhaseModel n) q q
  let p₀ := realGeodesicEndpointMap g d q
  let eD := extChartAt (realPhaseModel n) q
  let eC := extChartAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) p₀
  have hF := realGeodesicEndpointChartMap_contDiffAt g q d
  have hFD := realGeodesicEndpointChartMap_hasFDerivAt_equiv g q d hdet
  let c := hF.toOpenPartialHomeomorph F hFD (by simp)
  have hc₀ : z₀ ∈ c.source := hF.mem_toOpenPartialHomeomorph_source hFD (by simp)
  have hF₀ : F z₀ = eC p₀ := by
    dsimp only [F, realGeodesicEndpointChartMap, Function.comp_apply, z₀]
    rw [(extChartAt (realPhaseModel n) q).left_inv (mem_extChartAt_source q)]
  have hcInv₀ : c.symm (eC p₀) = z₀ := by
    rw [← hF₀]
    exact c.left_inv hc₀
  have hcInv : ContDiffAt ℝ 1 c.symm (eC p₀) := by
    rw [← hF₀]
    exact hF.to_localInverse hFD (by simp)
  let P := fun p : M.Carrier × M.Carrier => eD.symm (c.symm (eC p))
  have hP₀ : P p₀ = q := by
    dsimp only [P]
    rw [hcInv₀]
    exact eD.left_inv (mem_extChartAt_source q)
  have hC : ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      𝓘(ℝ, ComplexVector n × ComplexVector n) 1 eC p₀ := contMDiffAt_extChartAt
  have hDInv : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
      (realPhaseModel n) 1 eD.symm z₀ :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := realPhaseModel n) q).mem_nhds (mem_extChartAt_target q))
  have hP : ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (realPhaseModel n) 1 P p₀ := by
    have hmid := hcInv.contMDiffAt.comp p₀ hC
    have hDInv' : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
        (realPhaseModel n) 1 eD.symm (c.symm (eC p₀)) := by rw [hcInv₀]; exact hDInv
    exact hDInv'.comp p₀ hmid
  have hcTarget : eC p₀ ∈ c.target := by rw [← hF₀]; exact c.map_source hc₀
  have htargetN : ∀ᶠ p in 𝓝 p₀, eC p ∈ c.target :=
    hC.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds hcTarget)
  have hmapP : ContinuousAt (fun p => realGeodesicEndpointMap g d (P p)) p₀ :=
    (realGeodesicEndpointMap_contMDiff g d).continuous.continuousAt.comp hP.continuousAt
  have hsourceMap : realGeodesicEndpointMap g d (P p₀) ∈ eC.source := by
    rw [hP₀]
    exact mem_extChartAt_source p₀
  have hsourceMapN : ∀ᶠ p in 𝓝 p₀, realGeodesicEndpointMap g d (P p) ∈ eC.source :=
    hmapP.preimage_mem_nhds ((isOpen_extChartAt_source (I :=
      𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) p₀).mem_nhds hsourceMap)
  have hright : ∀ᶠ p in 𝓝 p₀, realGeodesicEndpointMap g d (P p) = p := by
    filter_upwards [htargetN, hsourceMapN, extChartAt_source_mem_nhds (I :=
      𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) p₀] with p hpC hpM hpS
    apply eC.injOn hpM hpS
    have h := c.right_inv hpC
    change F (c.symm (eC p)) = eC p at h
    exact h
  have hgood : ∀ᶠ p in 𝓝 p₀, ContMDiffAt
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P p :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ (∞ : ℕ∞ω))).mp hP
  have hN : ∀ᶠ p in 𝓝 p₀, realGeodesicEndpointMap g d (P p) = p ∧ ContMDiffAt
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P p := by
    filter_upwards [hright, hgood] with p hp hc
    exact ⟨hp, hc⟩
  obtain ⟨U, hU, hOpen, hpU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hOpen, hpU, P, (fun p hp => (hU hp).2.contMDiffWithinAt), hP₀, ?_, ?_⟩
  · intro p hp
    exact ⟨congrArg Prod.fst (hU hp).1, congrArg Prod.snd (hU hp).1⟩
  · have hDom : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) 1 eD q :=
      contMDiffAt_extChartAt
    have hDomN : ∀ᶠ q' in 𝓝 q, eD q' ∈ c.source :=
      hDom.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hc₀)
    filter_upwards [hDomN, extChartAt_source_mem_nhds (I := realPhaseModel n) q] with q' hcq hsq
    have hFq : F (eD q') = eC (realGeodesicEndpointMap g d q') := by
      dsimp only [F, realGeodesicEndpointChartMap, Function.comp_apply]
      rw [eD.left_inv hsq]
    have hcqInv : c.symm (F (eD q')) = eD q' := c.left_inv hcq
    dsimp only [P]
    rw [← hFq, hcqInv]
    exact eD.left_inv hsq

end Yau.LeafProofs.L12Aux
