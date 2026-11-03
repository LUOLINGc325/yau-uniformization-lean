import Yau.LeafProofs.L12BrokenEnergyFields

/-! Continuous concrete coefficients and the actual local first-derivative
field of the genuine three-segment energy. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def realBrokenCoefficient0 (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ) (a : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n →
      ComplexVector n →L[ℝ] (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n →L[ℝ] ℝ) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let X := fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
    chartPt a (realVelocityBaseFlow g p.proj u s)
  exact fun θ => ((ContinuousLinearMap.compL ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) (ComplexVector n) ℝ).flip
        ((fderiv ℝ X θ.1).comp (ContinuousLinearMap.fst ℝ _ _))).comp
          (realMetricInChart g.form a (X θ.1))

def realBrokenCoefficient1 (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (y : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n →
      ComplexVector n →L[ℝ] (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n →L[ℝ] ℝ) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  exact fun θ => ((ContinuousLinearMap.compL ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) (ComplexVector n) ℝ).flip
        (ContinuousLinearMap.snd ℝ _ _)).comp (realMetricInChart g.form y θ.2)

theorem realBrokenCoefficient0_continuousAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ) (a : M.Carrier)
    (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (ha : realVelocityBaseFlow g p.proj θ.1 s ∈ (chartAt (ComplexVector n) a).source) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContinuousAt (realBrokenCoefficient0 g p s a) θ := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let X := fun u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj =>
    chartPt a (realVelocityBaseFlow g p.proj u s)
  have hX : ContDiffAt ℝ 1 X θ.1 :=
    ((contMDiffAt_extChartAt' ha).comp θ.1
      (realVelocityBaseFlow_contMDiff g p.proj s θ.1)).contDiffAt
  have ht : X θ.1 ∈ chartTarget a :=
    (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source] using ha)
  have hB : ContinuousAt (fun q : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n =>
      realMetricInChart g.form a (X q.1)) θ :=
    ((realMetricInChart_smooth g a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds ht)).continuousAt.comp
        (f := fun q : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n => X q.1) (x := θ)
        (hX.continuousAt.comp (f := Prod.fst) (x := θ) continuousAt_fst)
  have hD : ContinuousAt (fun q : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n =>
      (fderiv ℝ X q.1).comp (ContinuousLinearMap.fst ℝ
        (TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (ComplexVector n))) θ :=
    ((hX.continuousAt_fderiv (by simp)).comp (f := Prod.fst) (x := θ)
      continuousAt_fst).clm_comp continuousAt_const
  exact continuousAt_metric_precomposition hB hD

theorem realBrokenCoefficient1_continuousAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (y : M.Carrier)
    (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (hy : θ.2 ∈ chartTarget y) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContinuousAt (realBrokenCoefficient1 g p y) θ := by
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hB : ContinuousAt (fun q : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n =>
      realMetricInChart g.form y q.2) θ :=
    ((realMetricInChart_smooth g y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds hy)).continuousAt.comp
        (f := Prod.snd) (x := θ) continuousAt_snd
  exact continuousAt_metric_precomposition hB continuousAt_const

/-- In the actual endpoint-branch neighborhood the genuine broken energy
has the concrete velocity-mismatch derivative field. -/
theorem realBrokenEndpointEnergy_firstDerivative_eventually (g : SmoothMetric M)
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
    ∀ᶠ u in 𝓝 θ, HasFDerivAt (realBrokenEndpointEnergy g p s e d P Q y z)
      (realBrokenCoefficient0 g p s a u (realBrokenMismatch0 g p s P a y u) +
        realBrokenCoefficient1 g p y u (realBrokenMismatch1 g p s e P Q y z u)) u := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hP hQ hPends hQends
  have hχ : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      𝓘(ℝ, ComplexVector n) 1 (fun u => chartInv y u.2) θ :=
    ((contMDiffAt_chartInv_real y θ.2 hy).of_le (by simp)).comp θ contDiffAt_snd.contMDiffAt
  have hA : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      𝓘(ℝ, ComplexVector n) 1 (fun u => realVelocityBaseFlow g p.proj u.1 s) θ :=
    (realVelocityBaseFlow_contMDiff g p.proj s θ.1).comp θ contDiffAt_fst.contMDiffAt
  have hNU := (hA.prodMk hχ).continuousAt.eventually (hU.mem_nhds hPU)
  have hzC : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      𝓘(ℝ, ComplexVector n) 1
      (fun _ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n => z) θ := contMDiffAt_const
  have hNV := (hχ.prodMk hzC).continuousAt.eventually (hV.mem_nhds hQV)
  have hNa := hA.continuousAt.eventually ((chartAt (ComplexVector n) a).open_source.mem_nhds ha)
  have hNy : ∀ᶠ u : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n in 𝓝 θ,
      u.2 ∈ chartTarget y :=
    continuousAt_snd.eventually ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds hy)
  filter_upwards [hNU, hNV, hNa, hNy] with u hu hv hau hyu
  exact realBrokenEndpointEnergy_hasFDerivAt g p s e d U V hU hV P Q a y z u
    hu hv hau hyu hP hQ hPends hQends

end Yau.LeafProofs.L12Aux
