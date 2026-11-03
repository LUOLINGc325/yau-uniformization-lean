import Yau.LeafProofs.L23FieldMetric

/-! Realize the actual complete smooth Kähler field as the existing SmoothMetric structure. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C05Aux

open Yau Set
open Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_from_real_coefficients (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (i j : Fin n) :
    hMat h x z i j = (realMetricFn h x z (i, 0) (j, 0) / 2 : ℂ) -
      Complex.I * (realMetricFn h x z (i, 0) (j, 1) / 2 : ℂ) := by
  rw [realMetricFn_entries, realMetricFn_entries]
  apply Complex.ext <;> simp
  ring

theorem smooth_field_complex_coefficients (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (chartCoefficientFunction h x i j) (chartTarget x) := by
  change ContDiffOn ℝ ∞ (fun z => hMat h x z i j) (chartTarget x)
  simp_rw [hMat_from_real_coefficients]
  have h₁ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hh x (i, 0) (j, 0)).div_const 2)
  have h₂ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hh x (i, 0) (j, 1)).div_const 2)
  convert h₁.sub ((contDiffOn_const (c := Complex.I)).mul h₂) using 1
  funext z
  simp [Complex.ofReal_div]

theorem chartVectorInFrame_eq_chartVec (a x : M.Carrier) (u : ComplexVector n) :
    chartVectorInFrame a x u = chartVec a x u := by
  have hu : ∑ i, u i • stdVec i = u := by
    ext j
    simp [stdVec, Pi.single_apply]
  let d : ComplexVector n →ₗ[ℂ] TangentVector M x :=
    ((mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
      (chartPt a x)).comp (tangentSpaceCastModel (ComplexModel n) (chartPt a x)).symm.toContinuousLinearMap).toLinearMap
  change (∑ i, u i • d (stdVec i)) = d u
  calc
    (∑ i, u i • d (stdVec i)) = d (∑ i, u i • stdVec i) := by simp only [map_sum, map_smul]
    _ = d u := congrArg d hu

theorem field_chartTransition (h : HermitianField M) : HermitianFieldChartTransition h := by
  intro a b x ha hb u v
  have ht (w : ComplexVector n) : chartVec b x (chartFrameChange b a x w) = chartVec a x w := by
    have hp : chartInv a (chartPt a x) = x := (extChartAt (ComplexModel n) a).left_inv ha
    have hz : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha
    have he := chartTransition_fderiv a b hz (hp.symm ▸ hb) w
    change chartFrameChange b a x w = _ at he
    rw [hp] at he
    rw [he]
    exact chartVec_tangentCoords b x hb _
  simp only [chartVectorInFrame_eq_chartVec, ht]

def smoothMetricOfCompleteField (h : HermitianField M) (hh : MetricSmooth h)
    (hcomplete : IsCompleteDistance (inducedDistance h)) (hK : KahlerClosed h) : SmoothMetric M := by
  letI := Yau.LeafProofs.L23Aux.metricSpaceOfField h hh
  exact
    { form := h
      coordinate_smooth := smooth_field_complex_coefficients h hh
      curve_nonempty := fun x y => by
        obtain ⟨γ⟩ := Yau.LeafProofs.L23Aux.integrable_curve_nonempty h hh x y
        exact ⟨γ.1⟩
      integrable_curve_nonempty := Yau.LeafProofs.L23Aux.integrable_curve_nonempty h hh
      chart_transition := field_chartTransition h
      induced_distance_nonneg := Yau.LeafProofs.L23Aux.inducedDistance_nonneg h hh
      induced_distance_eq_zero := by
        intro x y
        exact (dist_eq_zero : dist x y = 0 ↔ x = y)
      induced_distance_symm := Yau.LeafProofs.L23Aux.inducedDistance_symm h hh
      induced_distance_triangle := Yau.LeafProofs.L23Aux.inducedDistance_triangle h hh
      induced_distance_topology := by
        intro x s
        constructor
        · intro hs
          obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
          refine ⟨ε, hε, fun y hy => hball ?_⟩
          change inducedDistance h y x < ε
          rwa [Yau.LeafProofs.L23Aux.inducedDistance_symm h hh y x]
        · rintro ⟨ε, hε, hball⟩
          apply Metric.mem_nhds_iff.mpr
          refine ⟨ε, hε, fun y hy => hball ?_⟩
          change inducedDistance h x y < ε
          change inducedDistance h y x < ε at hy
          rwa [Yau.LeafProofs.L23Aux.inducedDistance_symm h hh y x] at hy
      complete_distance := hcomplete
      kahler_equations := hK }

theorem smoothMetricOfCompleteField_form (h : HermitianField M) (hh : MetricSmooth h)
    (hc : IsCompleteDistance (inducedDistance h)) (hK : KahlerClosed h) :
    (smoothMetricOfCompleteField h hh hc hK).form = h := rfl

theorem isCompact_complete_field_sublevel (h : HermitianField M) (hh : MetricSmooth h)
    (hc : IsCompleteDistance (inducedDistance h)) (hK : KahlerClosed h)
    (x : M.Carrier) (R : ℝ) : IsCompact {y | inducedDistance h x y ≤ R} :=
  isCompact_inducedDistance_sublevel (smoothMetricOfCompleteField h hh hc hK) x R

end Yau.Proofs.C05Aux
