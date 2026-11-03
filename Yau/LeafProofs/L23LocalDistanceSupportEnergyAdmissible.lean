import Yau.LeafProofs.L23LocalDistanceSupportEnergyDensity
import Yau.LeafProofs.L23LocalDistanceSupportSaturation

/-! Locally smooth paths have their genuine distance bound, by an admissible smooth saturation. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem fieldPathSpeed_continuous (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ → Continuous (fieldPathSpeed h γ) := by
  letI := manifold_realSmooth M
  intro hγ
  have H := continuous_norm_realCurveVelocity h hh hγ
  convert! H using 1

theorem fieldPathSpeed_sq_congr_eventuallyEq
    (h : HermitianField M) (γ β : ℝ → M.Carrier) (t : ℝ) (heq : γ =ᶠ[𝓝 t] β) :
    letI := manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ t →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β t →
    fieldPathSpeed h γ t ^ 2 = fieldPathSpeed h β t ^ 2 := by
  letI := manifold_realSmooth M
  intro hγ hβ
  let c := γ t
  have hγc : γ t ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hβc : β t ∈ (chartAt (ComplexVector n) c).source := by rw [← heq.self_of_nhds]; exact hγc
  have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (γ t) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1)
      (x := c) (x' := γ t) hγc) using 1
  have HD := ((HC.comp t hγ).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have HDβ := HD.congr_of_eventuallyEq ((heq.fun_comp (chartPt c)).symm)
  rw [fieldPathSpeed_sq_eq_chartDerivative h γ c t hγc _ (hγ.mdifferentiableAt (by norm_num)) HD,
    fieldPathSpeed_sq_eq_chartDerivative h β c t hβc _ (hβ.mdifferentiableAt (by norm_num)) HDβ,
    heq.self_of_nhds]

theorem fieldPathEnergy_congr_on_open
    (h : HermitianField M) (γ β : ℝ → M.Carrier) (J : Set ℝ) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) (heq : Set.EqOn γ β J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ J →
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β J →
    fieldPathEnergy h γ = fieldPathEnergy h β := by
  letI := manifold_realSmooth M
  intro hγ hβ
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have Hnear : γ =ᶠ[𝓝 u] β := eventually_of_mem (hJ.mem_nhds (hunit hu)) (fun r hr => heq hr)
  exact fieldPathSpeed_sq_congr_eventuallyEq h γ β u Hnear
    ((hγ u (hunit hu)).contMDiffAt (hJ.mem_nhds (hunit hu)))
    ((hβ u (hunit hu)).contMDiffAt (hJ.mem_nhds (hunit hu)))

theorem inducedDistance_sq_le_fieldPathEnergy_of_contMDiffOn
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (δ : ℝ) (hδ : 0 < δ) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Set.Ioo (-δ) (1+δ)) →
    inducedDistance h (γ 0) (γ 1)^2 ≤ fieldPathEnergy h γ := by
  letI := manifold_realSmooth M
  intro hγ
  obtain ⟨χ,hχ,hχmap,hχunit⟩ := exists_smooth_unit_saturation hδ
  let β := fun u => γ (χ u)
  have Hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β := by
    apply contMDiffOn_univ.mp
    exact hγ.comp ((hχ.of_le (by simp)).contMDiff.contMDiffOn) hχmap
  have hnear (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : γ =ᶠ[𝓝 u] β := by
    filter_upwards [hχunit u hu] with r hr
    change γ r = γ (χ r)
    rw [hr]
    rfl
  have hβ0 : β 0 = γ 0 := (hnear 0 (by norm_num)).self_of_nhds.symm
  have hβ1 : β 1 = γ 1 := (hnear 1 (by norm_num)).self_of_nhds.symm
  have Hspeed := fieldPathSpeed_continuous h hh β Hβ
  have H := inducedDistance_sq_le_fieldPathEnergy h hh (piecewiseC1Curve_of_contMDiff Hβ)
    (Hspeed.continuousOn.integrableOn_compact isCompact_Icc)
    ((Hspeed.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have HE : fieldPathEnergy h β = fieldPathEnergy h γ := by
    symm
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have huJ : u ∈ Set.Ioo (-δ) (1+δ) := by constructor <;> linarith [hu.1,hu.2]
    exact fieldPathSpeed_sq_congr_eventuallyEq h γ β u (hnear u hu)
      ((hγ u huJ).contMDiffAt (isOpen_Ioo.mem_nhds huJ)) (Hβ u)
  change inducedDistance h (β 0) (β 1)^2 ≤ fieldPathEnergy h β at H
  rwa [hβ0,hβ1,HE] at H

theorem fieldPathEnergy_eq_of_constant_actualSpeedSq (h : HermitianField M)
    (γ : ℝ → M.Carrier) (D : ℝ)
    (H : ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq h γ u = D) : fieldPathEnergy h γ = D := by
  have HE : fieldPathEnergy h γ = ∫ u in Set.Icc (0 : ℝ) 1, D := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [fieldPathSpeed_sq]
    exact H u hu
  simpa [integral_const,Measure.real] using HE

end Yau.LeafProofs.L23Aux
