import Yau.LeafProofs.L12HopfRinow
import Yau.LeafProofs.L23FieldMetricGeodesic

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

set_option backward.isDefEq.respectTransparency false in
theorem realGeodesicFlow_phase_chart_hasDerivAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (c : M.Carrier) (t : ℝ)
    (hc : (realGeodesicFlow g p t).proj ∈ (chartAt (ComplexVector n) c).source) :
    HasDerivAt (fun s => realPhaseChart c (realGeodesicFlow g p s))
      (chartGeodesicSpray g.form c (realPhaseChart c (realGeodesicFlow g p t))) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let pc : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨c, 0⟩
  let flow := realGeodesicFlow g p
  have hflow := realGeodesicFlow_integral g p
  have hsrc : flow t ∈ (extChartAt (realPhaseModel n) pc).source :=
    (realPhaseChart_source pc (flow t)).mpr hc
  have hsrc' : flow t ∈ (chartAt (ModelProd (ComplexVector n) (ComplexVector n)) pc).source := by
    simpa only [extChartAt_source] using hsrc
  have H : HasDerivAt ((extChartAt (realPhaseModel n) pc) ∘ flow)
      (tangentCoordChange (realPhaseModel n) (flow t) pc (flow t)
        (realGeodesicSpray g (flow t))) t := by
    rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
    apply (HasMFDerivAt.comp t
      (hasMFDerivAt_extChartAt (I := realPhaseModel n) hsrc')
      (hflow.isMIntegralCurveAt t).hasMFDerivAt).congr_mfderiv
    rw [ContinuousLinearMap.ext_iff]
    intro a
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
      ← one_apply_eq_self (F := TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t) a,
      ← ContinuousLinearMap.smulRight_apply, mfderiv_chartAt_eq_tangentCoordChange hsrc']
    rfl
  rw [tangentCoordChange_realGeodesicSpray g pc (flow t) hsrc] at H
  have heq : (fun s => realPhaseChart c (flow s)) =ᶠ[𝓝 t]
      (extChartAt (realPhaseModel n) pc) ∘ flow := by
    filter_upwards [hflow.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := realPhaseModel n) pc).mem_nhds hsrc)] with s hs
    exact (realPhaseChart_eq_extChartAt pc (flow s)
      ((realPhaseChart_source pc (flow s)).mp hs)).symm
  have hval : realPhaseChart c (flow t) = extChartAt (realPhaseModel n) pc (flow t) :=
    heq.self_of_nhds
  change HasDerivAt ((extChartAt (realPhaseModel n) pc) ∘ flow)
    (chartGeodesicSpray g.form c (extChartAt (realPhaseModel n) pc (flow t))) t at H
  rw [← hval] at H
  exact H.congr_of_eventuallyEq heq

set_option backward.isDefEq.respectTransparency false in
theorem realGeodesicFlow_fieldGeodesicOn (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (J : Set ℝ) :
    FieldGeodesicOn g.form (fun s => (realGeodesicFlow g p s).proj) J := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let γ : ℝ → M.Carrier := fun s => (realGeodesicFlow g p s).proj
  have hbase : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞ γ :=
    (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).comp (realGeodesicFlow_contMDiff g p)
  refine ⟨(hbase.of_le (by norm_num)).contMDiffOn, ?_⟩
  intro c t _ hc
  have hc' : γ t ∈ (chartAt (ComplexVector n) c).source := by
    simpa only [extChartAt_source] using hc
  have hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt (ComplexVector n) c).source :=
    hbase.continuous.continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds hc')
  have heq : geoChartState γ c =ᶠ[𝓝 t]
      (fun s => realPhaseChart c (realGeodesicFlow g p s)) := by
    filter_upwards [hsrc] with s hs
    apply Prod.ext
    · rfl
    · have HD : HasDerivAt (fun r => chartPt c (γ r))
          (realPhaseChart c (realGeodesicFlow g p s)).2 s :=
        (realGeodesicFlow_phase_chart_hasDerivAt g p c s hs).fst
      exact HD.deriv
  have H := realGeodesicFlow_phase_chart_hasDerivAt g p c t hc'
  have hval : geoChartState γ c t = realPhaseChart c (realGeodesicFlow g p t) :=
    heq.self_of_nhds
  rw [← hval] at H
  exact H.congr_of_eventuallyEq heq

theorem exists_minimizing_fieldGeodesic (g : SmoothMetric M)
    (q x : M.Carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M.Carrier,
      γ 0 = q ∧ γ 1 = x ∧
      FieldGeodesicOn g.form γ (Set.Ioo (-δ) (1 + δ)) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        actualSpeedSq g.form γ u = inducedDistance g.form q x ^ 2) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
        inducedDistance g.form (γ u) x ≤ (1 - u) * inducedDistance g.form q x) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨v, hv, hnorm⟩ := exists_minimizing_realExponential g q x
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨q, v⟩
  let γ : ℝ → M.Carrier := fun u => (realGeodesicFlow g p u).proj
  have hzero : γ 0 = q := by dsimp only [γ]; rw [realGeodesicFlow_zero]
  have hone : γ 1 = x := hv
  refine ⟨1, zero_lt_one, γ, hzero, hone,
    realGeodesicFlow_fieldGeodesicOn g p _, ?_, ?_⟩
  · intro u _
    dsimp only [actualSpeedSq]
    rw [realCurveVelocity_realGeodesic g (realGeodesicFlow g p)
      ((realGeodesicFlow_integral g p).isMIntegralCurveAt u)]
    change realTangentEnergy g.form (realGeodesicFlow g p u) = _
    rw [realGeodesicFlow_energy, realTangentEnergy_eq_norm_sq]
    exact congrArg (fun r : ℝ => r ^ 2) hnorm
  · intro u hu
    have H := realGeodesicFlow_base_dist_le g p u 1
    change inducedDistance g.form (γ u) (γ 1) ≤ ‖v‖ * |1 - u| at H
    rw [hone, hnorm, abs_of_nonneg (sub_nonneg.mpr hu.2)] at H
    simpa only [mul_comm] using H

end Yau.NodeProofs.P02Aux
