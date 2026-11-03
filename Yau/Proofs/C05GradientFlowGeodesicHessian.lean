import Yau.Proofs.C05GradientFlowHessian

/-! Along the genuine geodesic flow, the derivative of df on its velocity is Hess f. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

theorem tangentCoords_realTangentEquiv_self (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    tangentCoords x x (realTangentEquiv x v) = realTangentCoords x x v := by
  rw [realTangentCoords_self]
  have H := tangentCoords_chartVec x x (mem_extChartAt_source x)
    ((tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x) v)
  rw [chartVec_self] at H
  exact H

def scalarVelocity (f : M.Carrier → ℝ)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : ℝ :=
  mvfderiv 𝓘(ℝ, ComplexVector n) f p.proj p.2

theorem scalarVelocity_realGeodesic_hasDerivAt (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    HasDerivAt (fun s => scalarVelocity f (realGeodesicFlow g p s))
      (realHess g.form f (realGeodesicFlow g p t).proj
        (realTangentEquiv _ (realGeodesicFlow g p t).2)
        (realTangentEquiv _ (realGeodesicFlow g p t).2)) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let γ := realGeodesicFlow g p
  let c := (γ t).proj
  let η := extChartAt (realPhaseModel n) (γ t) ∘ γ
  have hγ := (realGeodesicFlow_integral g p).isMIntegralCurveAt t
  have hη := (realGeodesic_chart_eventually g γ hγ).self_of_nhds
  have hfc : ContDiffAt ℝ 2 (inChart c f) (η t).1 :=
    ((hf c).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds
      hη.1)).of_le (by simp)
  have H := chart_df_velocity_hasDerivAt g.form f c η t hfc hη.2
  have heq : (fun s => fderiv ℝ (inChart c f) (η s).1 (η s).2) =ᶠ[𝓝 t]
      (fun s => scalarVelocity f (γ s)) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realPhaseModel n) (γ t))] with s hs
    have hb := (realPhaseChart_source (γ t) (γ s)).mp hs
    dsimp only [η, Function.comp_apply]
    rw [realPhaseChart_eq_extChartAt (γ t) (γ s) hb]
    exact df_inChart_frame f hf c (γ s).proj hb (γ s).2
  have H' := heq.hasDerivAt_iff.mp H
  have hself : η t = realPhaseChart c (γ t) :=
    realPhaseChart_eq_extChartAt (γ t) (γ t) (mem_chart_source _ _)
  rw [hself] at H'
  simpa only [realHess_eq_scalarChartHessian g.form f hf,
    tangentCoords_realTangentEquiv_self, scalarVelocity, realPhaseChart] using H'

theorem realNormSq_realGeodesic_velocity (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realNormSq g.form (realGeodesicFlow g p t).proj
      (realTangentEquiv _ (realGeodesicFlow g p t).2) = realTangentEnergy g.form p := by
  change realTangentEnergy g.form (realGeodesicFlow g p t) = _
  exact realGeodesicFlow_energy g p t

end Yau.Proofs.C05GradientFlowAux
