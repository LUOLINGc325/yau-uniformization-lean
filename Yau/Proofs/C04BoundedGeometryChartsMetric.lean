import Yau.LeafProofs.L23FieldMetric
import Yau.Proofs.G04ScalarNormalization

/-! The genuine complete smooth metric and real pullback used by the
bounded-geometry chart construction. -/

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_of_realMetricFn (k : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b : Fin n) :
    hMat k x z a b = (realMetricFn k x z (a, 0) (b, 0) / 2 : ℂ) -
      Complex.I * (realMetricFn k x z (a, 0) (b, 1) / 2 : ℂ) := by
  rw [L12Aux.realMetricFn_entries, L12Aux.realMetricFn_entries]
  apply Complex.ext <;> simp <;> ring

theorem field_coordinate_smooth (k : HermitianField M) (hk : MetricSmooth k)
    (x : M.Carrier) (a b : Fin n) :
    ContDiffOn ℝ ∞ (chartCoefficientFunction k x a b)
      (extChartAt (ComplexModel n) x).target := by
  change ContDiffOn ℝ ∞ (fun z => hMat k x z a b) (chartTarget x)
  simp_rw [hMat_of_realMetricFn]
  have h₁ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hk x (a, 0) (b, 0)).div_const 2)
  have h₂ := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hk x (a, 0) (b, 1)).div_const 2)
  convert h₁.sub ((contDiffOn_const (c := Complex.I)).mul h₂) using 1
  funext z
  simp [Complex.ofReal_div]

theorem chartVectorInFrame_eq_chartVec (a x : M.Carrier) (u : ComplexVector n) :
    chartVectorInFrame a x u = chartVec a x u := by
  let d : ComplexVector n →ₗ[ℂ] TangentVector M x :=
    ((mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
      (chartPt a x)).comp (tangentSpaceCastModel (ComplexModel n) (chartPt a x)).symm.toContinuousLinearMap).toLinearMap
  have hu : ∑ i, u i • stdVec i = u := by
    ext j
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  change (∑ i, u i • d (stdVec i)) = d u
  calc
    _ = d (∑ i, u i • stdVec i) := by simp only [map_sum, map_smul]
    _ = d u := congrArg d hu

theorem hermitianField_chartTransition (k : HermitianField M) :
    HermitianFieldChartTransition k := by
  intro a b x ha hb u v
  have ht (w : ComplexVector n) : chartVec b x (chartFrameChange b a x w) = chartVec a x w := by
    have hp : chartInv a (chartPt a x) = x := (extChartAt (ComplexModel n) a).left_inv ha
    have hz : chartPt a x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha
    have he := L12Aux.chartTransition_fderiv a b hz (hp.symm ▸ hb) w
    change chartFrameChange b a x w = _ at he
    rw [hp] at he
    rw [he]
    exact L12Aux.chartVec_tangentCoords b x hb _
  simp only [chartVectorInFrame_eq_chartVec, ht]

def smoothMetric_of_complete_field (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hcomplete : IsCompleteDistance (lengthDist k)) : SmoothMetric M := by
  letI := L23Aux.metricSpaceOfField k hk
  exact
    { form := k
      coordinate_smooth := field_coordinate_smooth k hk
      curve_nonempty := fun x y => by
        obtain ⟨γ⟩ := L23Aux.integrable_curve_nonempty k hk x y
        exact ⟨γ.1⟩
      integrable_curve_nonempty := L23Aux.integrable_curve_nonempty k hk
      chart_transition := hermitianField_chartTransition k
      induced_distance_nonneg := L23Aux.inducedDistance_nonneg k hk
      induced_distance_eq_zero := by
        intro x y
        exact (dist_eq_zero : dist x y = 0 ↔ x = y)
      induced_distance_symm := L23Aux.inducedDistance_symm k hk
      induced_distance_triangle := L23Aux.inducedDistance_triangle k hk
      induced_distance_topology := by
        intro x s
        constructor
        · intro hs
          obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
          refine ⟨ε, hε, fun y hy => hball ?_⟩
          change inducedDistance k y x < ε
          rwa [L23Aux.inducedDistance_symm k hk y x]
        · rintro ⟨ε, hε, hball⟩
          apply Metric.mem_nhds_iff.mpr
          refine ⟨ε, hε, fun y hy => hball ?_⟩
          change inducedDistance k x y < ε
          change inducedDistance k y x < ε at hy
          rwa [L23Aux.inducedDistance_symm k hk y x] at hy
      complete_distance := hcomplete
      kahler_equations := hK }

@[simp] theorem smoothMetric_of_complete_field_form (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k)
    (hcomplete : IsCompleteDistance (lengthDist k)) :
    (smoothMetric_of_complete_field k hk hK hcomplete).form = k := rfl

/-- The actual real differential; the source tangent identification is explicit. -/
def realMapDeriv (E : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (E z) :=
  (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) E z).comp
    (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm.toContinuousLinearMap

/-- Real pullback of `G = 2 Re k`, including for nonholomorphic parametrizations. -/
def realPullbackMetric (k : HermitianField M) (E : ComplexVector n → M.Carrier)
    (z : ComplexVector n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun a b => (L12Aux.underlyingRealRiemannianMetric k).inner (E z)
    (realMapDeriv E z (realVec a)) (realMapDeriv E z (realVec b))

end Yau.Proofs.C04ChartsAux
