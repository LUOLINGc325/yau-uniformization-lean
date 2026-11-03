import Yau.LeafProofs.L12BrokenEndpointEnergy
import Yau.LeafProofs.L12EndpointEnergyComposition
import Yau.LeafProofs.L12BrokenHessianAnalysis

/-! The actual first derivative of the three-piece endpoint energy. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The derivative of the actual broken energy consists of the two true
velocity mismatches at its joints, paired using the actual metric. -/
theorem realBrokenEndpointEnergy_hasFDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e d : ℝ)
    (U V : Set (M.Carrier × M.Carrier)) (hU : IsOpen U) (hV : IsOpen V)
    (P Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (a y z : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (hPU : (realVelocityBaseFlow g p.proj θ.1 s, chartInv y θ.2) ∈ U)
    (hQV : (chartInv y θ.2, z) ∈ V)
    (ha : realVelocityBaseFlow g p.proj θ.1 s ∈ (chartAt (ComplexVector n) a).source)
    (hy : θ.2 ∈ chartTarget y) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 Q V →
    (∀ u ∈ U, (P u).proj = u.1 ∧ (realGeodesicFlow g (P u) e).proj = u.2) →
    (∀ u ∈ V, (Q u).proj = u.1 ∧ (realGeodesicFlow g (Q u) d).proj = u.2) →
    let q₀ := realGeodesicFlow g (⟨p.proj, θ.1⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s
    let q₁ := P (realVelocityBaseFlow g p.proj θ.1 s, chartInv y θ.2)
    let q₂ := realGeodesicFlow g q₁ e
    let q₃ := Q (chartInv y θ.2, z)
    let X := fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj => chartPt a (realVelocityBaseFlow g p.proj u s)
    HasFDerivAt (realBrokenEndpointEnergy g p s e d P Q y z)
      (((realMetricInChart g.form a (X θ.1)
          (realTangentCoords a q₀.proj q₀.2 - realTangentCoords a q₁.proj q₁.2)).comp
          ((fderiv ℝ X θ.1).comp (ContinuousLinearMap.fst ℝ _ _))) +
        ((realMetricInChart g.form y θ.2
          (realTangentCoords y q₂.proj q₂.2 - realTangentCoords y q₃.proj q₃.2)).comp
          (ContinuousLinearMap.snd ℝ _ _))) θ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hP hQ hPends hQends
  let q₀ := realGeodesicFlow g (⟨p.proj, θ.1⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s
  let q₁ := P (realVelocityBaseFlow g p.proj θ.1 s, chartInv y θ.2)
  let q₂ := realGeodesicFlow g q₁ e
  let q₃ := Q (chartInv y θ.2, z)
  let X := fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj => chartPt a (realVelocityBaseFlow g p.proj u s)
  let D := (fderiv ℝ X θ.1).comp (ContinuousLinearMap.fst ℝ
    (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n))
  have hXi : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj)
      𝓘(ℝ, ComplexVector n) 1 X θ.1 :=
    (contMDiffAt_extChartAt' ha).comp θ.1 (realVelocityBaseFlow_contMDiff g p.proj s θ.1)
  have hXD : HasFDerivAt (fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n => X u.1) D θ :=
    (hXi.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp θ
      (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n)).hasFDerivAt
  have hχ : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      𝓘(ℝ, ComplexVector n) 1 (fun u => chartInv y u.2) θ :=
    ((contMDiffAt_chartInv_real y θ.2 hy).of_le (by simp)).comp θ contDiffAt_snd.contMDiffAt
  have hχsrc : chartInv y θ.2 ∈ (chartAt (ComplexVector n) y).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) y).map_target hy
  have hchartχ : (fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n =>
      chartPt y (chartInv y u.2)) =ᶠ[𝓝 θ] Prod.snd := by
    filter_upwards [continuousAt_snd.eventually ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds hy)] with u hu
    exact (extChartAt (ComplexModel n) y).right_inv hu
  have hχD : HasFDerivAt
      (fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n => chartPt y (chartInv y u.2))
      (ContinuousLinearMap.snd ℝ _ _) θ :=
    hchartχ.hasFDerivAt_iff.mpr
      (ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n)).hasFDerivAt
  have hfirst := (realSegmentEnergy_fiber_hasFDerivAt g s p.proj a θ.1 ha).comp θ
    (ContinuousLinearMap.fst ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n)).hasFDerivAt
  let fP := fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n =>
    (realVelocityBaseFlow g p.proj u.1 s, chartInv y u.2)
  let fQ := fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n => (chartInv y u.2, z)
  have hfP : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 fP θ :=
    ((realVelocityBaseFlow_contMDiff g p.proj s θ.1).comp θ contDiffAt_fst.contMDiffAt).prodMk hχ
  have hfQ : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 fQ θ := hχ.prodMk contMDiffAt_const
  have hmid := realSegmentEnergy_endpointComposition_hasFDerivAt g e U hU P fP θ a y
    hPU ha hχsrc hP hPends hfP
  have hlast := realSegmentEnergy_endpointComposition_hasFDerivAt g d V hV Q fQ θ y z
    hQV hχsrc (mem_chart_source _ _) hQ hQends hfQ
  have hmidPair := hXD.prodMk hχD
  have hlastPair := hχD.prodMk (hasFDerivAt_const (chartPt z z) θ)
  rw [hmidPair.fderiv] at hmid
  rw [hlastPair.fderiv] at hlast
  have hsum := (hfirst.add hmid).add hlast
  have hp := hPends (fP θ) hPU
  have hq := hQends (fQ θ) hQV
  have hca : chartPt a q₁.proj = X θ.1 := congrArg (chartPt a) hp.1
  have hcb : chartPt y q₂.proj = θ.2 := (congrArg (chartPt y) hp.2).trans hchartχ.self_of_nhds
  have hcc : chartPt y q₃.proj = θ.2 := (congrArg (chartPt y) hq.1).trans hchartχ.self_of_nhds
  apply hsum.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  change ((realChartMomentum g a q₀).comp D +
    ((-realChartMomentum g a q₁).coprod (realChartMomentum g y q₂)).comp
      (D.prod (ContinuousLinearMap.snd ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n))) +
    ((-realChartMomentum g y q₃).coprod
      (realChartMomentum g z (realGeodesicFlow g q₃ d))).comp
        ((ContinuousLinearMap.snd ℝ
          (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n)).prod
          (0 : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n →L[ℝ] ComplexVector n))) h = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, map_zero, add_zero, neg_apply]
  dsimp only [realChartMomentum]
  rw [hca, hcb, hcc]
  simp only [map_sub, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  dsimp only [D, X, q₀, q₁, q₂, q₃, realVelocityBaseFlow, ContinuousLinearMap.comp_apply]
  ring

end Yau.LeafProofs.L12Aux
