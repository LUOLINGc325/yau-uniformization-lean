import Yau.Proofs.F01HolomorphicKahlerJet
import Yau.Proofs.F01KahlerJetSymmetry
import Yau.LeafProofs.L17HolomorphicCharts

/-! The genuine metric pullback has Kähler first-jet symmetry in every
actual holomorphic chart, not just its original center-dependent frame. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothMetric_pullback_wirt_symm (g : SmoothMetric M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (i j k : Fin n) :
    wirt (fun w => pullbackMatrix g.form e w i j) z (stdVec k) =
      wirt (fun w => pullbackMatrix g.form e w i k) z (stdVec j) := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hzD : z ∈ forwardChartDomain e a := ⟨hz, ha⟩
  have hT : ContDiffAt ℂ 2 T z := ((forwardChart_contDiffOn e he a).contDiffAt
    ((forwardChartDomain_isOpen e a).mem_nhds hzD)).of_le (by simp)
  have htarget : T z ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha
  have hH (p q : Fin n) : DifferentiableAt ℝ (fun y => hMat g.form a y p q) (T z) :=
    ((hMat_contDiffOn_of_metricSmooth g.form
      (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g) a p q).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds htarget)).differentiableAt
      (by simp)
  have hsym (p q l : Fin n) : wirt (fun y => hMat g.form a y p q) (T z) (stdVec l) =
      wirt (fun y => hMat g.form a y p l) (T z) (stdVec q) :=
    smoothMetric_hMat_wirt_symm g a (T z) htarget l q p
  have hgerm (p q : Fin n) : (fun w => pullbackMatrix g.form e w p q) =ᶠ[𝓝 z]
      (fun w => ((linearMatrix (fderiv ℂ T w))ᴴ * hMat g.form a (T w) *
        linearMatrix (fderiv ℂ T w)) p q) := by
    filter_upwards [(forwardChartDomain_isOpen e a).mem_nhds hzD] with w hw
    have hc := pullbackMatrix_eq_congruence g.form e a w hw.2
    rw [coordinateDifferential_eq_fderiv e he a hw.1 hw.2] at hc
    exact congrFun (congrFun hc p) q
  have hwirt (p q : Fin n) (v : ComplexVector n) :
      wirt (fun w => pullbackMatrix g.form e w p q) z v =
        wirt (fun w => ((linearMatrix (fderiv ℂ T w))ᴴ * hMat g.form a (T w) *
          linearMatrix (fderiv ℂ T w)) p q) z v := by
    unfold wirt
    rw [(hgerm p q).fderiv_eq]
  rw [hwirt, hwirt]
  exact holomorphic_congruence_wirt_symmetry (hMat g.form a) T z hT hH hsym i j k

end Yau.NodeProofs.F01Aux
