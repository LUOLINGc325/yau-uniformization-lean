import Yau.Proofs.C05GradientFlowGradient

/-! Actual local gradient integral curves are C1 in fixed charts. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000

theorem realTangentCoords_eq_tangentCoordChange (c x : M.Carrier)
    (hx : x ∈ (chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    realTangentCoords c x = tangentCoordChange 𝓘(ℝ, ComplexVector n) x c x := by
  letI := manifold_realSmooth M
  unfold realTangentCoords
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]

theorem gradient_integral_chart_eventually (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (γ : ℝ → M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    IsMIntegralCurveAt γ (realGradientVectorField g.form f) t →
      ∀ᶠ s in 𝓝 t, chartPt (γ t) (γ s) ∈ chartTarget (γ t) ∧
        HasDerivAt (fun u => chartPt (γ t) (γ u))
          (realGradInChart g.form f (γ t) (chartPt (γ t) (γ s))) s := by
  letI := manifold_realSmooth M
  intro hγ
  filter_upwards [hγ.eventually_hasDerivAt,
    hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℝ, ComplexVector n)) (γ t))] with s hs hsrc
  have hb : γ s ∈ (chartAt (ComplexVector n) (γ t)).source := by
    simpa only [extChartAt_source, Set.mem_preimage] using hsrc
  refine ⟨(extChartAt (ComplexModel n) (γ t)).map_source hsrc, ?_⟩
  have hcoords : tangentCoordChange 𝓘(ℝ, ComplexVector n) (γ s) (γ t) (γ s)
      (realGradientVectorField g.form f (γ s)) =
        realGradInChart g.form f (γ t) (chartPt (γ t) (γ s)) := by
    calc
      _ = realTangentCoords (γ t) (γ s) (realGradientVectorField g.form f (γ s)) :=
        congrArg (fun L => L (realGradientVectorField g.form f (γ s)))
          (realTangentCoords_eq_tangentCoordChange (γ t) (γ s) hb).symm
      _ = _ := by
        rw [realGradientVectorField_eq_local g.form f hf (γ t) (γ s) hb]
        exact localGradientVectorField_coordinates g.form f (γ t) (γ s) hb
  convert hs using 1 <;> first | rfl | exact hcoords.symm

theorem gradient_integral_contMDiffAt_one (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (γ : ℝ → M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    IsMIntegralCurveAt γ (realGradientVectorField g.form f) t →
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ t := by
  letI := manifold_realSmooth M
  intro hγ
  let c := γ t
  let η := fun s => chartPt c (γ s)
  let S := {s | η s ∈ chartTarget c ∧
    HasDerivAt η (realGradInChart g.form f c (η s)) s}
  have hS : S ∈ 𝓝 t := gradient_integral_chart_eventually g f hf γ t hγ
  have hcoef : ContinuousOn (fun s => realGradInChart g.form f c (η s)) S := by
    intro s hs
    exact (((realGradInChart_contDiffOn g f hf c).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hs.1)).comp
        hs.2.continuousAt).continuousWithinAt
  have hη : ContDiffAt ℝ 1 η t := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fun s => (1 : ℝ →L[ℝ] ℝ).smulRight
      (realGradInChart g.form f c (η s)), S, hS, ?_, ?_⟩
    · exact (ContinuousLinearMap.smulRightL ℝ ℝ (ComplexVector n)
        (1 : ℝ →L[ℝ] ℝ)).continuous.comp_continuousOn hcoef
    · intro s hs
      exact hs.2.hasFDerivAt
  have hi := (contMDiffAt_chartInv_real c (chartPt c c) (mem_extChartAt_target c)).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have H := hi.comp t hη.contMDiffAt
  apply H.congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := 𝓘(ℝ, ComplexVector n)) c)] with s hs
  exact ((extChartAt (ComplexModel n) c).left_inv hs).symm

end Yau.Proofs.C05GradientFlowAux
