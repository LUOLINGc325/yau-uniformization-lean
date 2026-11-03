import Yau.LeafProofs.L12EndpointEnergyComposition
import Yau.LeafProofs.L12JacobiMatrixODE
import Yau.LeafProofs.L12PhaseCoordinates

/-! Second order endpoint energy from the actual first variation.  Only
the proved C1 dependence of the geodesic phase flow is used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- First variation for a genuine fixed-base branch with endpoint coordinates
as parameter.  The assertion holds at every point of the open branch domain. -/
theorem realSegmentEnergy_endpoint_hasFDerivAt
    (g : SmoothMetric M) (d : ℝ) (a b : M.Carrier)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hb : z ∈ chartTarget b) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O →
    (∀ y ∈ O, (Q y).proj = a ∧
      (realGeodesicFlow g (Q y) d).proj = chartInv b y) →
    HasFDerivAt (realSegmentEnergy g d ∘ Q)
      (realChartMomentum g b (realGeodesicFlow g (Q z) d)) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ hends
  have hN : ∀ᶠ y in 𝓝 z, y ∈ O := hO.mem_nhds hz
  have hq := hQ.contMDiffAt (hO.mem_nhds hz)
  have hs : (realGeodesicFlow g (Q z) d).proj ∈
      (chartAt (ComplexVector n) b).source := by
    rw [(hends z hz).2]
    simpa only [extChartAt_source, chartInv] using
      (extChartAt (ComplexModel n) b).map_target hb
  have h := realSegmentEnergy_fixedBase_hasFDerivAt g d Q z b hq (by
    filter_upwards [hN] with y hy
    exact (hends y hy).1.trans (hends z hz).1.symm) hs
  have heq : (fun y => chartPt b (realGeodesicFlow g (Q y) d).proj) =ᶠ[𝓝 z] id := by
    filter_upwards [hN, (isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hb]
      with y hy hby
    rw [(hends y hy).2]
    exact (extChartAt (ComplexModel n) b).right_inv hby
  rw [heq.fderiv_eq, fderiv_id, ContinuousLinearMap.comp_id] at h
  exact h

/-- The terminal momentum of a genuine C1 branch is a C1 covector field. -/
theorem realSegmentEnergy_endpointMomentum_contDiffAt
    (g : SmoothMetric M) (d : ℝ) (b : M.Carrier)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (z : ComplexVector n)
    (hb : (realGeodesicFlow g (Q z) d).proj ∈ (chartAt (ComplexVector n) b).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q z →
    ContDiffAt ℝ 1 (fun y => realChartMomentum g b (realGeodesicFlow g (Q y) d)) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ
  have hflow : ContMDiffAt 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1
      (fun y => realGeodesicFlow g (Q y) d) z :=
    (realGeodesicFlow_joint_contMDiff g (Q z, d)).comp z
      (hQ.prodMk contMDiffAt_const)
  exact (((realChartMomentum_contMDiffAt g b _ hb).of_le (by simp)).comp z hflow).contDiffAt

/-- Actual segment energy is C2 in the endpoint on a C1 endpoint branch.
The derivative witness is supplied on a whole neighborhood. -/
theorem realSegmentEnergy_endpoint_contDiffAt_two
    (g : SmoothMetric M) (d : ℝ) (a b : M.Carrier)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hb : z ∈ chartTarget b) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O →
    (∀ y ∈ O, (Q y).proj = a ∧
      (realGeodesicFlow g (Q y) d).proj = chartInv b y) →
    ContDiffAt ℝ 2 (realSegmentEnergy g d ∘ Q) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ hends
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).2
  refine ⟨fun y => realChartMomentum g b (realGeodesicFlow g (Q y) d), ?_, ?_⟩
  · refine ⟨O ∩ chartTarget b, inter_mem (hO.mem_nhds hz)
        ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hb), ?_⟩
    intro y hy
    exact realSegmentEnergy_endpoint_hasFDerivAt g d a b Q O hO y hy.1 hy.2 hQ hends
  · apply realSegmentEnergy_endpointMomentum_contDiffAt g d b Q z _
      (hQ.contMDiffAt (hO.mem_nhds hz))
    rw [(hends z hz).2]
    simpa only [extChartAt_source, chartInv] using
      (extChartAt (ComplexModel n) b).map_target hb

/-- Metric compatibility converts the derivative of the actual momentum
into the covariant scalar Hessian. -/
theorem covariantHessian_eq_of_endpointMomentum
    (g : SmoothMetric M) (b : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget b) (s : ℝ) (f : ComplexVector n → ℝ)
    (V : ComplexVector n → ComplexVector n)
    (hV : DifferentiableAt ℝ V z)
    (hdf : (fderiv ℝ f) =ᶠ[𝓝 z]
      (fun y => s • realMetricInChart g.form b y (V y)))
    (u v : ComplexVector n) :
    fderiv ℝ (fderiv ℝ f) z u v -
        fderiv ℝ f z (chartChristoffelBilin g.form b z u v) =
      s * realMetricInChart g.form b z
        (fderiv ℝ V z u + chartChristoffelBilin g.form b z u (V z)) v := by
  have hG := ((realMetricInChart_smooth g b).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hz)).differentiableAt (by simp)
  have hD := (hG.hasFDerivAt.clm_apply hV.hasFDerivAt).const_smul s
  have hDeq := hD.fderiv
  change fderiv ℝ (fun y => s • realMetricInChart g.form b y (V y)) z = _ at hDeq
  rw [hdf.fderiv_eq, hDeq, hdf.eq_of_nhds]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [realMetricInChart_connection_compatibility g b z hz u (V z) v]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

/-- E1 for the scaled energy of a genuine fixed-base endpoint branch. -/
theorem realSegmentEnergy_endpoint_covariantHessian
    (g : SmoothMetric M) (d s : ℝ) (a b : M.Carrier)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n)
    (hz : z ∈ O) (hb : z ∈ chartTarget b) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O →
    (∀ y ∈ O, (Q y).proj = a ∧
      (realGeodesicFlow g (Q y) d).proj = chartInv b y) →
    ∀ u v : ComplexVector n,
    let f := fun y => s * realSegmentEnergy g d (Q y)
    let V := fun y => realChartVelocity b (realGeodesicFlow g (Q y) d)
    fderiv ℝ (fderiv ℝ f) z u v -
        fderiv ℝ f z (chartChristoffelBilin g.form b z u v) =
      s * realMetricInChart g.form b z
        (fderiv ℝ V z u + chartChristoffelBilin g.form b z u (V z)) v := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hQ hends u v
  have hq := hQ.contMDiffAt (hO.mem_nhds hz)
  have hs : (realGeodesicFlow g (Q z) d).proj ∈
      (chartAt (ComplexVector n) b).source := by
    rw [(hends z hz).2]
    simpa only [extChartAt_source, chartInv] using
      (extChartAt (ComplexModel n) b).map_target hb
  have hflow : ContMDiffAt 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1
      (fun y => realGeodesicFlow g (Q y) d) z :=
    (realGeodesicFlow_joint_contMDiff g (Q z, d)).comp z
      (hq.prodMk contMDiffAt_const)
  have hCv : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1
      (realChartVelocity b) (realGeodesicFlow g (Q z) d) :=
    (realChartVelocity_contMDiffAt b _ hs).of_le (by simp)
  have hVC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (fun y => realChartVelocity b (realGeodesicFlow g (Q y) d)) z :=
    hCv.comp z hflow
  have hV : DifferentiableAt ℝ
      (fun y => realChartVelocity b (realGeodesicFlow g (Q y) d)) z :=
    hVC.contDiffAt.differentiableAt (by simp)
  apply covariantHessian_eq_of_endpointMomentum g b z hb s _ _ hV
  filter_upwards [hO.mem_nhds hz,
    (isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds hb] with y hy hby
  have hD := (realSegmentEnergy_endpoint_hasFDerivAt g d a b Q O hO y hy hby hQ hends).const_mul s
  simp only [Function.comp_apply] at hD
  rw [hD.fderiv]
  have hc : chartPt b (realGeodesicFlow g (Q y) d).proj = y := by
    rw [(hends y hy).2]
    exact (extChartAt (ComplexModel n) b).right_inv hby
  simp only [realChartMomentum, realChartVelocity, hc]

/-- A genuine C1 phase branch with fixed initial point is represented by a
genuine C1 map into that fixed tangent fiber. -/
theorem realFixedBaseBranch_exists_velocityBranch
    (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (Q : ComplexVector n → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (z : ComplexVector n) (hz : z ∈ O) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn 𝓘(ℝ, ComplexVector n) (realPhaseModel n) 1 Q O →
    (∀ y ∈ O, (Q y).proj = p.proj) → Q z = p →
    ∃ W : ComplexVector n → TangentSpace 𝓘(ℝ, ComplexVector n) p.proj,
      ContDiffOn ℝ 1 W O ∧ W z = p.2 ∧
      ∀ y ∈ O, (⟨p.proj, W y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = Q y := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hQ hbase hQz
  let W := fun y => realFrameCLM p.proj p.proj (realChartVelocity p.proj (Q y))
  have hW : ContDiffOn ℝ 1 W O := by
    intro y hy
    have hs : (Q y).proj ∈ (chartAt (ComplexVector n) p.proj).source := by
      rw [hbase y hy]
      exact mem_chart_source _ _
    have hC : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) 1
        (realChartVelocity p.proj) (Q y) :=
      (realChartVelocity_contMDiffAt p.proj (Q y) hs).of_le (by simp)
    have hV : ContDiffAt ℝ 1 (fun t => realChartVelocity p.proj (Q t)) y :=
      (hC.comp y (hQ.contMDiffAt (hO.mem_nhds hy))).contDiffAt
    exact ((realFrameCLM p.proj p.proj).contDiff.contDiffAt.comp y hV).contDiffWithinAt
  refine ⟨W, hW, ?_, ?_⟩
  · dsimp only [W]
    rw [hQz]
    exact realFrameCLM_realTangentCoords p.proj p.proj (mem_chart_source _ _) p.2
  · intro y hy
    have hby := hbase y hy
    change (⟨p.proj, realFrameCLM p.proj p.proj
      (realTangentCoords p.proj (Q y).proj (Q y).2)⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = Q y
    generalize Q y = q at hby ⊢
    cases q with | mk b v =>
      dsimp at hby
      subst b
      rw [realFrameCLM_realTangentCoords p.proj p.proj (mem_chart_source _ _)]

end Yau.LeafProofs.L19Aux
