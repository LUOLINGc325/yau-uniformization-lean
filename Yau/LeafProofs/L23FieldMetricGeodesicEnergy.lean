import Yau.LeafProofs.L23FieldMetricNormalBranchCurve
import Yau.LeafProofs.L23FieldMetricUnitLength

/-! Actual manifold geodesics have constant physical speed and the expected unit length. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem actualSpeedSq_eq_chartEnergy (h : HermitianField M) (γ : ℝ → M.Carrier)
    (c : M.Carrier) (t : ℝ) (hc : γ t ∈ (chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ t →
    actualSpeedSq h γ t = chartGeodesicEnergy h c (geoChartState γ c t) := by
  letI := manifold_realSmooth M
  intro hγ
  have Hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (γ t) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1) (x := c) (x' := γ t) hc) using 1
  have HD := (((Hchart.comp t hγ).contDiffAt).differentiableAt (by norm_num)).hasDerivAt
  have Hcoords := realCurveVelocity_coords_of_hasDerivAt γ t c _ hc (hγ.mdifferentiableAt (by norm_num)) HD
  have Hmetric := realMetricInChart_tangentCoords h c (γ t) hc (realCurveVelocity γ t) (realCurveVelocity γ t)
  rw [Hcoords] at Hmetric
  exact Hmetric.symm

theorem actualSpeedSq_nonneg (h : HermitianField M) (γ : ℝ → M.Carrier) (t : ℝ) :
    0 ≤ actualSpeedSq h γ t := by
  letI := underlyingRealTangentNormedAddCommGroup h (γ t)
  letI := underlyingRealTangentInnerProductSpace h (γ t)
  change 0 ≤ inner ℝ (realCurveVelocity γ t) (realCurveVelocity γ t)
  exact real_inner_self_nonneg

theorem fieldGeodesic_actualSpeedSq_hasDerivAt_zero
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (hJ : IsOpen J) (hγ : FieldGeodesicOn h γ J) (t : ℝ) (ht : t ∈ J) :
    HasDerivAt (actualSpeedSq h γ) 0 t := by
  letI := manifold_realSmooth M
  let c := γ t
  have hcont : ContinuousAt γ t := hγ.1.continuousOn.continuousAt (hJ.mem_nhds ht)
  have hsrc : ∀ᶠ u in 𝓝 t, γ u ∈ (chartAt (ComplexVector n) c).source :=
    hcont.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _))
  have hEq : actualSpeedSq h γ =ᶠ[𝓝 t] (fun u => chartGeodesicEnergy h c (geoChartState γ c u)) := by
    filter_upwards [hJ.mem_nhds ht,hsrc] with u hu hcu
    exact actualSpeedSq_eq_chartEnergy h γ c u hcu
      (((hγ.1 u hu).contMDiffAt (hJ.mem_nhds hu)).of_le (by norm_num))
  have H := chartGeodesicEnergy_hasDerivAt h hh c (geoChartState γ c)
    (mem_extChartAt_target c) (hγ.2 c t ht (mem_extChartAt_source c))
  exact H.congr_of_eventuallyEq hEq

theorem fieldGeodesic_actualSpeedSq_constant
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    {a b s t : ℝ} (hγ : FieldGeodesicOn h γ (Set.Ioo a b))
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) : actualSpeedSq h γ s = actualSpeedSq h γ t := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
  · intro u hu
    exact (fieldGeodesic_actualSpeedSq_hasDerivAt_zero h hh γ _ isOpen_Ioo hγ u hu).differentiableAt.differentiableWithinAt
  · intro u hu
    exact (fieldGeodesic_actualSpeedSq_hasDerivAt_zero h hh γ _ isOpen_Ioo hγ u hu).deriv
  · exact hs
  · exact ht

theorem fieldGeodesic_unit_pathELength
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    {ε : ℝ} (hε : 0 < ε) (hγ : FieldGeodesicOn h γ (Set.Ioo (-ε) (1+ε))) :
    fieldPathELength h γ 0 1 = ENNReal.ofReal (Real.sqrt (actualSpeedSq h γ 0)) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hnorm (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ‖realCurveVelocity γ u‖ = Real.sqrt (actualSpeedSq h γ 0) := by
    have hu' : u ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith [hu.1,hu.2]
    have HE := fieldGeodesic_actualSpeedSq_constant h hh γ hγ hu' h₀
    have Hnorm : ‖realCurveVelocity γ u‖^2 = actualSpeedSq h γ u := (real_inner_self_eq_norm_sq _).symm
    rw [← HE,← Hnorm,Real.sqrt_sq (norm_nonneg _)]
  change Manifold.pathELength 𝓘(ℝ, ComplexVector n) γ 0 1 = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hEq : (fun u => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ u 1‖ₑ) =ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) 1)] (fun _ => ENNReal.ofReal (Real.sqrt (actualSpeedSq h γ 0))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [← ofReal_norm]
    exact congrArg ENNReal.ofReal (hnorm u hu)
  rw [lintegral_congr_ae hEq]
  simp

end Yau.LeafProofs.L23Aux
