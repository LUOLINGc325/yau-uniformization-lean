import Yau.LeafProofs.L17HolomorphicCharts

/-! Smoothness of the actual metric pullback uses one fixed ordinary chart
near the point. No regularity of a center-dependent choice of frame is used. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem pullbackMatrix_entry_contDiffAt (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => pullbackMatrix g e w i j) z := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hzT : z ∈ forwardChartDomain e a := ⟨hz, ha⟩
  have hT : ContDiffAt ℂ ∞ T z :=
    (forwardChart_contDiffOn e he a).contDiffAt
      ((forwardChartDomain_isOpen e a).mem_nhds hzT)
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hT.fderiv_right (by simp)
  have hJ (p q : Fin n) : ContDiffAt ℝ ∞
      (fun w => linearMatrix (fderiv ℂ T w) p q) z :=
    (((EuclideanSpace.proj p : ComplexVector n →L[ℂ] ℂ).contDiff.contDiffAt.comp z
      (hD.clm_apply contDiffAt_const)).restrict_scalars ℝ)
  have hG (p q : Fin n) : ContDiffAt ℝ ∞ (fun w => hMat g a (T w) p q) z := by
    have hga : ContDiffAt ℝ ∞ (fun y => hMat g a y p q) (T z) :=
      (hMat_contDiffOn_of_metricSmooth g hg a p q).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
        ((extChartAt (ComplexModel n) a).map_source ha))
    exact hga.comp z (hT.restrict_scalars ℝ)
  have hterm (p q : Fin n) : ContDiffAt ℝ ∞
      (fun w => star (linearMatrix (fderiv ℂ T w) p i) * hMat g a (T w) p q *
        linearMatrix (fderiv ℂ T w) q j) z :=
    ((Complex.conjCLE.contDiff.contDiffAt.comp z (hJ p i)).mul (hG p q)).mul (hJ q j)
  have hs : ContDiffAt ℝ ∞ (fun w =>
      ((linearMatrix (fderiv ℂ T w))ᴴ * hMat g a (T w) *
        linearMatrix (fderiv ℂ T w)) i j) z := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul] using
      (ContDiffAt.sum (fun q (_ : q ∈ Finset.univ) =>
        ContDiffAt.sum (fun p (_ : p ∈ Finset.univ) => hterm p q)))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(forwardChartDomain_isOpen e a).mem_nhds hzT] with w hw
  have hc := pullbackMatrix_eq_congruence g e a w hw.2
  rw [coordinateDifferential_eq_fderiv e he a hw.1 hw.2] at hc
  exact congrFun (congrFun hc i) j

theorem pullbackMatrix_entry_contDiffOn (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun w => pullbackMatrix g e w i j) e.source :=
  fun _ hz => (pullbackMatrix_entry_contDiffAt g hg e he hz i j).contDiffWithinAt

end Yau.NodeProofs.F01Aux
