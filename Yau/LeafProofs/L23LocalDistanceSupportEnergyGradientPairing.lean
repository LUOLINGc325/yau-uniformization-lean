import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradientCoordinate

/-! Pairing a true geodesic velocity with a true parallel variation vector is constant. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem geodesic_parallel_pairing_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (V : (u : ℝ) → TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (J : Set ℝ) (hJ : IsOpen J) (hγ : FieldGeodesicOn h γ J)
    (hV : ∀ (c : M.Carrier) (u : ℝ), u ∈ J → γ u ∈ (chartAt (ComplexVector n) c).source →
      HasDerivAt (fun s => realTangentCoords c (γ s) (V s))
        (-chartChristoffelBilin h c (chartPt c (γ u)) (geoChartState γ c u).2
          (realTangentCoords c (γ u) (V u))) u)
    (t : ℝ) (ht : t ∈ J) :
    HasDerivAt (fun u => (underlyingRealRiemannianMetric h).inner (γ u) (realCurveVelocity γ u) (V u)) 0 t := by
  letI := manifold_realSmooth M
  let c := γ t
  let Z := fun u => chartPt c (γ u)
  let T := fun u => deriv Z u
  let W := fun u => realTangentCoords c (γ u) (V u)
  have hc : γ t ∈ (extChartAt (ComplexModel n) c).source := mem_extChartAt_source _
  have Hphase := hγ.2 c t ht hc
  have HZ : HasDerivAt Z (T t) t := by
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t Hphase using 1
  have HT : HasDerivAt T (-chartChristoffelBilin h c (Z t) (T t) (T t)) t := by
    convert! (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t Hphase using 1
    exact (chartGeodesicAcceleration_eq h c (Z t) (T t)).symm
  have HW := hV c t ht (mem_chart_source _ _)
  have H := chartGeodesic_pairing_hasDerivAt h hh c (mem_extChartAt_target c) HZ HT HW
  change HasDerivAt (fun s => realMetricInChart h c (Z s) (T s) (W s))
    (realMetricInChart h c (Z t) (T t)
      (-chartChristoffelBilin h c (Z t) (T t) (W t)+chartChristoffelBilin h c (Z t) (T t) (W t))) t at H
  simp only [neg_add_cancel,map_zero] at H
  have hcont : ContinuousAt γ t := hγ.1.continuousOn.continuousAt (hJ.mem_nhds ht)
  have Hnear : ∀ᶠ u in 𝓝 t, u ∈ J ∧ γ u ∈ (chartAt (ComplexVector n) c).source :=
    inter_mem (hJ.mem_nhds ht) (hcont.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _)))
  apply H.congr_of_eventuallyEq
  filter_upwards [Hnear] with u hu
  have hγu : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
    ((hγ.1 u hu.1).contMDiffAt (hJ.mem_nhds hu.1)).of_le (by norm_num)
  have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (γ u) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1) (x := c) (x' := γ u) hu.2) using 1
  have HD := ((HC.comp u hγu).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have HV := realCurveVelocity_coords_of_hasDerivAt γ u c (T u) hu.2 (hγu.mdifferentiableAt (by norm_num)) HD
  have HM := realMetricInChart_tangentCoords h c (γ u) hu.2 (realCurveVelocity γ u) (V u)
  rw [HV] at HM
  exact HM.symm

theorem geodesic_parallel_pairing_constant
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (V : (u : ℝ) → TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (a b : ℝ) (hγ : FieldGeodesicOn h γ (Set.Ioo a b))
    (hV : ∀ (c : M.Carrier) (u : ℝ), u ∈ Set.Ioo a b → γ u ∈ (chartAt (ComplexVector n) c).source →
      HasDerivAt (fun s => realTangentCoords c (γ s) (V s))
        (-chartChristoffelBilin h c (chartPt c (γ u)) (geoChartState γ c u).2
          (realTangentCoords c (γ u) (V u))) u)
    (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    (underlyingRealRiemannianMetric h).inner (γ s) (realCurveVelocity γ s) (V s) =
      (underlyingRealRiemannianMetric h).inner (γ t) (realCurveVelocity γ t) (V t) := by
  have HD := geodesic_parallel_pairing_hasDerivAt h hh γ V _ isOpen_Ioo hγ hV
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun u hu => (HD u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (HD u hu).deriv) hs ht

end Yau.LeafProofs.L23Aux
