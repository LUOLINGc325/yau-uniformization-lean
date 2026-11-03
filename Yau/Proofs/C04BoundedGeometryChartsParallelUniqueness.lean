import Yau.Proofs.C04BoundedGeometryChartsRadialComplex
import Yau.Proofs.C04BoundedGeometryChartsRadialGauge

/-! Actual parallel sections along the same genuine geodesic have unique initial values. -/

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem parallel_sections_unique (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (Q R : (t : ℝ) → TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g q t).proj)
    (hQ : ∀ t, HasDerivAt
      (fun s => realTangentCoords (realGeodesicFlow g q t).proj (realGeodesicFlow g q s).proj (Q s))
      (-chartChristoffelBilin g.form (realGeodesicFlow g q t).proj
        (chartPt (realGeodesicFlow g q t).proj (realGeodesicFlow g q t).proj)
        (realTangentCoords (realGeodesicFlow g q t).proj (realGeodesicFlow g q t).proj
          (realGeodesicFlow g q t).2)
        (realTangentCoords (realGeodesicFlow g q t).proj (realGeodesicFlow g q t).proj (Q t))) t)
    (hR : ∀ t, HasDerivAt
      (fun s => realTangentCoords (realGeodesicFlow g q t).proj (realGeodesicFlow g q s).proj (R s))
      (-chartChristoffelBilin g.form (realGeodesicFlow g q t).proj
        (chartPt (realGeodesicFlow g q t).proj (realGeodesicFlow g q t).proj)
        (realTangentCoords (realGeodesicFlow g q t).proj (realGeodesicFlow g q t).proj
          (realGeodesicFlow g q t).2)
        (realTangentCoords (realGeodesicFlow g q t).proj (realGeodesicFlow g q t).proj (R t))) t)
    (hQR₀ : realTangentCoords q.proj (realGeodesicFlow g q 0).proj (Q 0) =
      realTangentCoords q.proj (realGeodesicFlow g q 0).proj (R 0)) : ∀ t, Q t = R t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let W : (t : ℝ) → TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g q t).proj :=
    fun t => Q t - R t
  let F := fun t => (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g q t).proj (W t) (W t)
  have hF (t : ℝ) : HasDerivAt F 0 t := by
    let c := (realGeodesicFlow g q t).proj
    let Z := fun s => realTangentCoords c (realGeodesicFlow g q s).proj (Q s) -
      realTangentCoords c (realGeodesicFlow g q s).proj (R s)
    have hZ : HasDerivAt Z
        (-chartChristoffelBilin g.form c (chartPt c c)
          (realTangentCoords c c (realGeodesicFlow g q t).2) (Z t)) t := by
      convert (hQ t).sub (hR t) using 1
      simp only [Z, map_sub]
      abel
    have H := realMetricInChart_parallelPair_hasDerivAt g c (mem_extChartAt_target c)
      (realGeodesicFlow_baseCoords_hasDerivAt g q t) hZ hZ
    apply H.congr_of_eventuallyEq
    have hn := (((FiberBundle.continuous_proj (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).comp (realGeodesicFlow_contMDiff g q).continuous).continuousAt
      (x := t)).preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [hn] with s hs
    have hW : realTangentCoords c (realGeodesicFlow g q s).proj (W s) = Z s := by
      simp only [W, Z, map_sub]
    exact (realMetricInChart_tangentCoords g.form c (realGeodesicFlow g q s).proj hs (W s) (W s)).symm.trans
      (by rw [hW])
  have hsrc₀ : (realGeodesicFlow g q 0).proj ∈ (chartAt (ComplexVector n) q.proj).source := by
    rw [realGeodesicFlow_zero]
    exact mem_chart_source _ _
  have hW₀ : W 0 = 0 := by
    have H := congrArg (realFrameCLM q.proj (realGeodesicFlow g q 0).proj) hQR₀
    simp only [realFrameCLM_realTangentCoords _ _ hsrc₀] at H
    exact sub_eq_zero.mpr H
  have hF₀ : F 0 = 0 := by simp only [F, hW₀, map_zero, ContinuousLinearMap.zero_apply]
  intro t
  let A := |t| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have h₀ : (0 : ℝ) ∈ Ioo (-A) A := ⟨by linarith, hA⟩
  have ht : t ∈ Ioo (-A) A := abs_lt.mp (lt_add_one |t|)
  have hconst : F t = F 0 := isOpen_Ioo.is_const_of_deriv_eq_zero
    (convex_Ioo (-A) A).isPreconnected
    (fun s _ => (hF s).differentiableAt.differentiableWithinAt) (fun s _ => (hF s).deriv) ht h₀
  have hWt : W t = 0 := by
    by_contra hnot
    have H := (underlyingRealRiemannianMetric g.form).pos (realGeodesicFlow g q t).proj (W t) hnot
    change 0 < F t at H
    rw [hconst, hF₀] at H
    exact lt_irrefl 0 H
  exact sub_eq_zero.mp hWt

theorem parallelUnitaryFrame_velocity (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) (t : ℝ) :
    parallelUnitaryFrame g p U v t v = (realGeodesicFlow g (radialInitialState p U v) t).2 := by
  let q := radialInitialState p U v
  apply parallel_sections_unique g q (fun s => parallelUnitaryFrame g p U v s v)
    (fun s => (realGeodesicFlow g q s).2)
  · intro s
    exact parallelUnitaryFrame_coordinates_hasDerivAt g p U v v s
  · intro s
    have HP := Yau.NodeProofs.P02Aux.realGeodesicFlow_phase_chart_hasDerivAt g q
      (realGeodesicFlow g q s).proj s (mem_chart_source _ _)
    have H : HasDerivAt (fun a => (realPhaseChart (realGeodesicFlow g q s).proj (realGeodesicFlow g q a)).2)
        (chartGeodesicSpray g.form (realGeodesicFlow g q s).proj
          (realPhaseChart (realGeodesicFlow g q s).proj (realGeodesicFlow g q s))).2 s := by
      have Hraw := HP.snd
      have heq (a : ComplexVector n × ComplexVector n) :
          (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).comp
              (ContinuousLinearMap.toSpanSingleton ℝ a) =
            ContinuousLinearMap.toSpanSingleton ℝ a.2 := by
        apply ContinuousLinearMap.ext
        intro b
        rfl
      rw [heq] at Hraw
      exact Hraw
    simpa only [realPhaseChart, chartGeodesicSpray, chartGeodesicAcceleration_eq] using H
  · have H := parallelUnitaryFrame_initial_coordinates g p U v v
    have Hq := congrArg (fun z : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
      realTangentCoords p z.proj z.2) (realGeodesicFlow_zero g q)
    exact H.trans Hq.symm

theorem radialCoframe_radial (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    radialCoframe g p U v v = v := by
  have HD := unitaryExponential_chart_radial_fderiv g p U v
  have Hcoords := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L v)
    (realMapDeriv_coordinates g p U (unitaryExponential g p U v) v (mem_chart_source _ _))
  have H := congrArg (realFrameCLM (unitaryExponential g p U v) (unitaryExponential g p U v))
    (Hcoords.trans HD)
  simp only [ContinuousLinearMap.comp_apply, realFrameCLM_realTangentCoords _ _ (mem_chart_source _ _)] at H
  have Hdv : realMapDeriv (unitaryExponential g p U) v v = radialParallelFrame g p U v v := by
    exact H.trans (parallelUnitaryFrame_velocity g p U v 1).symm
  change (radialParallelFrame g p U v).symm (realMapDeriv (unitaryExponential g p U) v v) = v
  rw [Hdv]
  exact (radialParallelFrame g p U v).symm_apply_apply v

end Yau.Proofs.C04ChartsAux
