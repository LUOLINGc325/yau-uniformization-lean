import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradientCoordinate

/-! The true inverse-metric gradient norm of an endpoint momentum covector. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem chartGradientPair_eq_four_physical_normSq
    (h : HermitianField M) (x : M.Carrier) (f : ComplexVector n → ℝ)
    (T : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hD : ∀ w : ComplexVector n, fderiv ℝ f (chartPt x x) w =
      2*realMetricInChart h x (chartPt x x) (realTangentCoords x x T) w) :
    chartGradientPair h x f f (chartPt x x) =
      4*(underlyingRealRiemannianMetric h).inner x T T := by
  letI := underlyingRealTangentNormedAddCommGroup h x
  letI := underlyingRealTangentInnerProductSpace h x
  let b := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)
  rw [chartGradientPair_self_eq_orthonormal_sum h x f b]
  simp_rw [hD,realMetricInChart_tangentCoords h x x (mem_chart_source _ _)]
  change (∑ i, (2*inner ℝ T (b i))^2) = 4*inner ℝ T T
  simp_rw [mul_pow]
  rw [← Finset.mul_sum,b.sum_sq_inner_left,real_inner_self_eq_norm_sq]
  norm_num

theorem endpointChart_hasFDerivAt_id
    (y : M.Carrier) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (F : ComplexVector n → M.Carrier) (h0 : (0 : ComplexVector n) ∈ e.source)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hL : L = realFrameCLM y y) (hend : Set.EqOn F e e.source)
    (hF : HasFDerivAt (fun v => chartPt y (F v)) ((realTangentCoords y y).comp L) 0) :
    HasFDerivAt (fun v => chartPt y (e v)) (ContinuousLinearMap.id ℝ (ComplexVector n)) 0 := by
  have HL : (realTangentCoords y y).comp L = ContinuousLinearMap.id ℝ (ComplexVector n) := by
    rw [hL]
    apply ContinuousLinearMap.ext
    intro v
    exact realTangentCoords_realFrameCLM y y (mem_chart_source _ _) v
  rw [HL] at hF
  apply hF.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds h0] with v hv
  exact congrArg (chartPt y) (hend hv).symm

theorem realGradPair_of_endpoint_parameter_directions
    (h : HermitianField M) (y : M.Carrier) (E : M.Carrier → ℝ) (Eu : ComplexVector n → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (hDe : HasFDerivAt (fun v => chartPt y (e v)) (ContinuousLinearMap.id ℝ (ComplexVector n)) 0)
    (hEu : Set.EqOn Eu (fun v => E (e v)) e.source)
    (hE : DifferentiableAt ℝ (inChart y E) (chartPt y y))
    (T : TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hdir : ∀ w : ComplexVector n, HasDerivAt (fun r : ℝ => Eu (r • w))
      (2*realMetricInChart h y (chartPt y y) (realTangentCoords y y T) w) 0) :
    realGradPair h E E y = 4*(underlyingRealRiemannianMetric h).inner y T T := by
  have Hpoint : chartPt y (e 0) = chartPt y y := congrArg (chartPt y) he0
  have HF : HasFDerivAt (inChart y E) (fderiv ℝ (inChart y E) (chartPt y y)) (chartPt y (e 0)) := by
    rw [Hpoint]
    exact hE.hasFDerivAt
  have H := HF.comp 0 hDe
  simp only [ContinuousLinearMap.comp_id] at H
  have Hecont := e.continuousAt h0
  have Hsource : ∀ᶠ v in 𝓝 (0 : ComplexVector n), e v ∈ (extChartAt (ComplexModel n) y).source :=
    Hecont.preimage_mem_nhds (by rw [he0]; exact (isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds (mem_extChartAt_source y))
  have HEq : Eu =ᶠ[𝓝 (0 : ComplexVector n)] (inChart y E ∘ fun v => chartPt y (e v)) := by
    filter_upwards [e.open_source.mem_nhds h0,Hsource] with v hv hvs
    rw [hEu hv]
    change E (e v) = E (chartInv y (chartPt y (e v)))
    exact congrArg E ((extChartAt (ComplexModel n) y).left_inv hvs).symm
  have HParam := H.congr_of_eventuallyEq HEq
  apply chartGradientPair_eq_four_physical_normSq h y (inChart y E) T
  intro w
  have HL : HasDerivAt (fun r : ℝ => r • w) w 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have HF0 : HasFDerivAt Eu (fderiv ℝ (inChart y E) (chartPt y y)) ((0 : ℝ) • w) := by
    simpa only [zero_smul] using HParam
  have HD := (HF0.comp_hasDerivAt 0 HL).unique (hdir w)
  exact HD

end Yau.LeafProofs.L23Aux
