import Yau.Proofs.C05GradientFlowFirstVariation

/-! Hessian concavity gives the actual two-endpoint distance Dini inequality. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1600000

theorem gradient_pair_distance_upperRightSlopeLE (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier) (a r : ℝ) (hr : 0 < r)
    (hHess : ∀ x ∈ distBall g.form o (2 * r), ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (α β : ℝ → M.Carrier) (t : ℝ)
    (hx : α t ∈ gradientTrap g o r) (hy : β t ∈ gradientTrap g o r) :
    letI := manifold_realSmooth M
    IsMIntegralCurveAt α (realGradientVectorField g.form f) t →
    IsMIntegralCurveAt β (realGradientVectorField g.form f) t →
    UpperRightSlopeLE (fun s => inducedDistance g.form (α s) (β s)) t
      (-a * inducedDistance g.form (α t) (β t)) := by
  letI := manifold_realSmooth M
  intro hα hβ
  by_cases hxy : α t = β t
  · have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      ((realGradientVectorField_contMDiff g f hf).of_le (by simp)).contMDiffAt hα hβ hxy
    have hz : inducedDistance g.form (α t) (β t) = 0 := g.induced_distance_eq_zero.mpr hxy
    have hbound : ∀ᶠ s in 𝓝[>] t, inducedDistance g.form (α s) (β s) ≤ (0 : ℝ) := by
      filter_upwards [heq.filter_mono nhdsWithin_le_nhds] with s hs
      exact (g.induced_distance_eq_zero.mpr hs).le
    have H := upperRightSlopeLE_of_upper_support hz hbound (hasDerivAt_const t (0 : ℝ))
    simpa only [hz, mul_zero] using H
  · have hD : 0 < inducedDistance g.form (α t) (β t) :=
      lt_of_le_of_ne (g.induced_distance_nonneg _ _)
        (Ne.symm (fun h => hxy (g.induced_distance_eq_zero.mp h)))
    letI := underlyingRealTangentNormedAddCommGroup g.form (α t)
    obtain ⟨v, hve, hvn, hbuffer⟩ := exists_trap_minimizing_segment g o hr (α t) (β t) hx hy
    let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨α t, v⟩
    have hend : (realGeodesicFlow g p 1).proj = β t := hve
    have hmin : realTangentEnergy g.form p = inducedDistance g.form (α t) (β t) ^ 2 := by
      rw [realTangentEnergy_eq_norm_sq]
      exact congrArg (fun q : ℝ => q ^ 2) hvn
    have hregion : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (realGeodesicFlow g p s).proj ∈ distBall g.form o (2 * r) := by
      intro s hs
      have H := (hbuffer s hs).2
      rwa [realExponentialMap_smul] at H
    have hv := (gradient_integral_chart_eventually g f hf α t hα).self_of_nhds.2
    have hw := (gradient_integral_chart_eventually g f hf β t hβ).self_of_nhds.2
    have H := endpoint_distance_upperRightSlopeLE g p α β t
      (realGradInChart g.form f p.proj (chartPt p.proj p.proj))
      (realGradInChart g.form f (realGeodesicFlow g p 1).proj
        (chartPt (realGeodesicFlow g p 1).proj (realGeodesicFlow g p 1).proj))
      rfl hend.symm hD hmin (gradient_integral_contMDiffAt_one g f hf α t hα)
      (gradient_integral_contMDiffAt_one g f hf β t hβ) hv (by simpa only [hend] using hw)
    rw [realChartMomentum_gradient g f hf p.proj p (mem_chart_source _ _),
      realChartMomentum_gradient g f hf (realGeodesicFlow g p 1).proj
        (realGeodesicFlow g p 1) (mem_chart_source _ _)] at H
    apply H.mono
    apply (div_le_iff₀ hD).mpr
    have HFTC := scalarVelocity_geodesic_difference_le g f hf a
      (distBall g.form o (2 * r)) hHess p hregion
    rw [hmin] at HFTC
    nlinarith only [HFTC]

end Yau.Proofs.C05GradientFlowAux
