import Yau.Proofs.C02ParallelGaugeSmooth
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Coefficients of the actual radial parallel frame are smooth in every
valid fixed target chart. The real coordinate chart need not contain the
whole image of the exponential parametrization. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalParallelCoefficients (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (realTangentCoords c (normalRealMap g p U x)).comp
    (normalParallelIsometry g p U hU x).toContinuousLinearMap

theorem normalParallelCoefficients_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (normalParallelCoefficients g p U hU c)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let O := (normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source
  have hO : IsOpen O :=
    (chartAt (ComplexVector n) c).open_source.preimage (normalRealMap_smooth g p U hU).continuous
  apply contDiffOn_clm_apply.mpr
  intro z x hx
  let q₀ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨c, 0⟩
  let e := extChartAt (realPhaseModel n) q₀
  have hsrc : normalParallelTotalSpace g p U hU (x, z) ∈ e.source :=
    (realPhaseChart_source q₀ _).mpr hx
  have hchart : ContMDiffAt (realPhaseModel n)
      𝓘(ℝ, ComplexVector n × ComplexVector n) ∞ e
      (normalParallelTotalSpace g p U hU (x, z)) :=
    contMDiffAt_extChartAt' (by simpa only [e, extChartAt_source] using hsrc)
  have hin : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
      (fun y => (y, z)) x := contMDiffAt_id.prodMk_space contMDiffAt_const
  have hP := (normalParallelTotalSpace_smooth g p U hU).contMDiffAt.comp x hin
  have hcomp : ContMDiffAt 𝓘(ℝ, ComplexVector n)
      𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
      (fun y => e (normalParallelTotalSpace g p U hU (y, z))) x :=
    hchart.comp x hP
  have hEval := (contMDiffAt_iff_contDiffAt.mp hcomp).snd
  have hevent : (fun y => normalParallelCoefficients g p U hU c y z) =ᶠ[𝓝 x]
      (fun y => (e (normalParallelTotalSpace g p U hU (y, z))).2) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    have hc := realPhaseChart_eq_extChartAt q₀ (normalParallelTotalSpace g p U hU (y, z)) hy
    exact congrArg Prod.snd hc.symm
  exact (hEval.congr_of_eventuallyEq hevent).contDiffWithinAt

end Yau.Blueprint.C02Proof
