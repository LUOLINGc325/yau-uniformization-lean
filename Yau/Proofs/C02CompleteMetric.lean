import Yau.Proofs.C02MetricSlice
import Yau.Proofs.C02Frames
import Yau.LeafProofs.L23FieldMetric

/-! The record below uses the same supplied field. Every field is proved from its
actual smoothness, closed Kähler equations and complete length distance. -/
noncomputable section
open Set Filter
open scoped Manifold Topology ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

 theorem field_coordinate_smooth
    (k : HermitianField M) (hk : MetricSmooth k) (a : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (chartCoefficientFunction k a i j) (chartTarget a) := by
  have hr := (contDiffOn_const.mul (hk a (i, 0) (j, 0)) :
    ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * realMetricFn k a z (i, 0) (j, 0)) _)
  have hi := (contDiffOn_const.mul (hk a (i, 1) (j, 0)) :
    ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℝ) * realMetricFn k a z (i, 1) (j, 0)) _)
  have h := (Complex.ofRealCLM.contDiff.comp_contDiffOn hr).add
    ((contDiffOn_const (c := Complex.I)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hi))
  apply h.congr
  intro z hz
  change hMat k a z i j = _
  apply Complex.ext <;>
    simp [L12Aux.realMetricFn_entries, Complex.mul_re, Complex.mul_im]

 theorem field_chartTransition (k : HermitianField M) : HermitianFieldChartTransition k := by
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

 def smoothMetricOfField (k : HermitianField M) (hk : MetricSmooth k)
    (hcomplete : IsCompleteDistance (inducedDistance k)) (hKahler : KahlerClosed k) :
    SmoothMetric M := by
  letI := L23Aux.metricSpaceOfField k hk
  exact
    { form := k
      coordinate_smooth := field_coordinate_smooth k hk
      curve_nonempty := fun x y => by
        obtain ⟨γ⟩ := L23Aux.integrable_curve_nonempty k hk x y
        exact ⟨γ.1⟩
      integrable_curve_nonempty := L23Aux.integrable_curve_nonempty k hk
      chart_transition := field_chartTransition k
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
      kahler_equations := hKahler }

 @[simp] theorem smoothMetricOfField_form (k : HermitianField M) (hk : MetricSmooth k)
    (hcomplete : IsCompleteDistance (inducedDistance k)) (hKahler : KahlerClosed k) :
    (smoothMetricOfField k hk hcomplete hKahler).form = k := rfl

 def completeFlowSlice (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (hflow : IsKahlerRicciFlow X.metric.form h)
    (hC01 : HarnackCompleteness X o h) (t : ℝ) (ht : 0 < t) :
    SmoothMetric X.manifold :=
  smoothMetricOfField (h t)
    (metricFamilySmooth_slice hflow.2.1 ht.le)
    (hC01.2.1 t ht) (hflow.2.2.1 t ht.le)

 @[simp] theorem completeFlowSlice_form (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (hflow : IsKahlerRicciFlow X.metric.form h)
    (hC01 : HarnackCompleteness X o h) (t : ℝ) (ht : 0 < t) :
    (completeFlowSlice X o h hflow hC01 t ht).form = h t := rfl

end Yau.Blueprint.C02Proof
