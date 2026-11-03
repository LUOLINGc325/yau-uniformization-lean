import Yau.LeafProofs.L12BrokenEndpointDifferential
import Yau.LeafProofs.L12PhaseCoordinates

/-! The genuine phase and velocity-mismatch fields of the finite broken
energy. All regularity is obtained from the actual flow and endpoint branches. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Continuous metric and endpoint-derivative coefficients give a continuous
coefficient for the true velocity-mismatch derivative field. -/
theorem continuousAt_metric_precomposition
    {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : S → E →L[ℝ] E →L[ℝ] ℝ} {D : S → S →L[ℝ] E} {z : S}
    (hB : ContinuousAt B z) (hD : ContinuousAt D z) :
    ContinuousAt (fun q => ((ContinuousLinearMap.compL ℝ S E ℝ).flip (D q)).comp (B q)) z := by
  have hc : ContinuousAt (fun q => (ContinuousLinearMap.compL ℝ S E ℝ).flip (D q)) z :=
    ((ContinuousLinearMap.compL ℝ S E ℝ).flip.continuous.continuousAt).comp
      (f := D) (x := z) hD
  exact hc.clm_comp hB

def realBrokenPhaseFirst (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ)
    (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) :=
  realGeodesicFlow g (⟨p.proj, θ.1⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s

def realBrokenPhaseMiddle (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) :=
  P ((realBrokenPhaseFirst g p s θ).proj, chartInv y θ.2)

def realBrokenPhaseLast
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y z : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) :=
  Q (chartInv y θ.2, z)

def realBrokenMismatch0 (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (a y : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) :=
  realChartVelocity a (realBrokenPhaseFirst g p s θ) -
    realChartVelocity a (realBrokenPhaseMiddle g p s P y θ)

def realBrokenMismatch1 (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e : ℝ)
    (P Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y z : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n) :=
  realChartVelocity y (realGeodesicFlow g (realBrokenPhaseMiddle g p s P y θ) e) -
    realChartVelocity y (realBrokenPhaseLast p Q y z θ)

theorem realBrokenPhaseFirst_contMDiff (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      (realPhaseModel n) 1 (realBrokenPhaseFirst g p s) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  exact (realVelocityFlow_contMDiff g p.proj s).comp contDiff_fst.contMDiff

theorem realBrokenPhaseMiddle_contMDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ)
    (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (hy : θ.2 ∈ chartTarget y)
    (hPU : ((realBrokenPhaseFirst g p s θ).proj, chartInv y θ.2) ∈ U) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      (realPhaseModel n) 1 (realBrokenPhaseMiddle g p s P y) θ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hP
  exact (hP.contMDiffAt (hU.mem_nhds hPU)).comp θ
    (((realVelocityBaseFlow_contMDiff g p.proj s θ.1).comp θ contDiffAt_fst.contMDiffAt).prodMk
      (((contMDiffAt_chartInv_real y θ.2 hy).of_le (by simp)).comp θ contDiffAt_snd.contMDiffAt))

theorem realBrokenPhaseLast_contMDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (V : Set (M.Carrier × M.Carrier)) (hV : IsOpen V)
    (Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y z : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (hy : θ.2 ∈ chartTarget y) (hQV : (chartInv y θ.2, z) ∈ V) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 Q V →
    ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
      (realPhaseModel n) 1 (realBrokenPhaseLast p Q y z) θ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hQ
  exact (hQ.contMDiffAt (hV.mem_nhds hQV)).comp θ
    ((((contMDiffAt_chartInv_real y θ.2 hy).of_le (by simp)).comp θ
      contDiffAt_snd.contMDiffAt).prodMk contMDiffAt_const)

/-- The first actual mismatch is C1 on the endpoint-branch neighborhood. -/
theorem realBrokenMismatch0_contDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s : ℝ)
    (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (a y : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (hy : θ.2 ∈ chartTarget y)
    (hPU : ((realBrokenPhaseFirst g p s θ).proj, chartInv y θ.2) ∈ U)
    (ha₀ : (realBrokenPhaseFirst g p s θ).proj ∈ (chartAt (ComplexVector n) a).source)
    (ha₁ : (realBrokenPhaseMiddle g p s P y θ).proj ∈ (chartAt (ComplexVector n) a).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    ContDiffAt ℝ 1 (realBrokenMismatch0 g p s P a y) θ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hP
  exact ((((realChartVelocity_contMDiffAt a _ ha₀).of_le (by simp)).comp θ
    (realBrokenPhaseFirst_contMDiff g p s θ)).contDiffAt).sub
    ((((realChartVelocity_contMDiffAt a _ ha₁).of_le (by simp)).comp θ
      (realBrokenPhaseMiddle_contMDiffAt g p s U hU P y θ hy hPU hP)).contDiffAt)

/-- The second actual mismatch is C1 on the endpoint-branch neighborhood. -/
theorem realBrokenMismatch1_contDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s e : ℝ)
    (U V : Set (M.Carrier × M.Carrier)) (hU : IsOpen U) (hV : IsOpen V)
    (P Q : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (y z : M.Carrier) (θ : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj × ComplexVector n)
    (hy : θ.2 ∈ chartTarget y)
    (hPU : ((realBrokenPhaseFirst g p s θ).proj, chartInv y θ.2) ∈ U)
    (hQV : (chartInv y θ.2, z) ∈ V)
    (hy₀ : (realGeodesicFlow g (realBrokenPhaseMiddle g p s P y θ) e).proj ∈ (chartAt (ComplexVector n) y).source)
    (hy₁ : (realBrokenPhaseLast p Q y z θ).proj ∈ (chartAt (ComplexVector n) y).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 Q V →
    ContDiffAt ℝ 1 (realBrokenMismatch1 g p s e P Q y z) θ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  intro hP hQ
  have hmid := realBrokenPhaseMiddle_contMDiffAt g p s U hU P y θ hy hPU hP
  have hterminal := (realGeodesicPhaseFlow_contMDiff g e _).comp θ hmid
  exact ((((realChartVelocity_contMDiffAt y _ hy₀).of_le (by simp)).comp θ
    hterminal).contDiffAt).sub
    ((((realChartVelocity_contMDiffAt y _ hy₁).of_le (by simp)).comp θ
      (realBrokenPhaseLast_contMDiffAt g p V hV Q y z θ hy hQV hQ)).contDiffAt)

end Yau.LeafProofs.L12Aux
