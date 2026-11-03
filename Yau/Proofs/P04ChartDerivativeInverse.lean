import Yau.Proofs.P04CanonicalOverlap
import Yau.LeafProofs.L17RicciNaturality

noncomputable section
open Set Filter WithLp
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The inverse derivative comes from the actual two chart inverses. -/
theorem chartTransition_fderiv_leftInverse (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    (fderiv ℂ (fun w => chartPt a (chartInv b w)) (chartPt b (chartInv a z))).comp
      (fderiv ℂ (fun w => chartPt b (chartInv a w)) z) =
        ContinuousLinearMap.id ℂ (ComplexVector n) := by
  have hT := L18Aux.chartTransition_contDiffAt a b hz hy
  have htz : chartPt b (chartInv a z) ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hy
  have hsinv : chartInv b (chartPt b (chartInv a z))=chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  have hsa : chartInv b (chartPt b (chartInv a z)) ∈ (extChartAt (ComplexModel n) a).source := by
    rw [hsinv]
    exact (extChartAt (ComplexModel n) a).map_target hz
  have hS := L18Aux.chartTransition_contDiffAt b a htz hsa
  have heq : ((fun w => chartPt a (chartInv b w)) ∘ (fun w => chartPt b (chartInv a w)))
      =ᶠ[𝓝 z] id := by
    filter_upwards [(canonicalOverlap_isOpen b a).mem_nhds ⟨hz,hy⟩] with w hw
    change chartPt a (chartInv b (chartPt b (chartInv a w)))=w
    rw [show chartInv b (chartPt b (chartInv a w))=chartInv a w from
      (extChartAt (ComplexModel n) b).left_inv hw.2]
    exact (extChartAt (ComplexModel n) a).right_inv hw.1
  have hcomp := fderiv_comp z (hS.differentiableAt (by simp)) (hT.differentiableAt (by simp))
  have hid := heq.fderiv_eq (𝕜 := ℂ)
  simpa only [fderiv_id] using hcomp.symm.trans hid

theorem chartTransition_fderiv_injective (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    Function.Injective (fderiv ℂ (fun w => chartPt b (chartInv a w)) z) := by
  intro v w hvw
  have H := congrArg (fderiv ℂ (fun w => chartPt a (chartInv b w)) (chartPt b (chartInv a z))) hvw
  change ((fderiv ℂ (fun w => chartPt a (chartInv b w)) (chartPt b (chartInv a z))).comp
    (fderiv ℂ (fun w => chartPt b (chartInv a w)) z)) v =
    ((fderiv ℂ (fun w => chartPt a (chartInv b w)) (chartPt b (chartInv a z))).comp
    (fderiv ℂ (fun w => chartPt b (chartInv a w)) z)) w at H
  rw [chartTransition_fderiv_leftInverse a b hz hy] at H
  exact H

theorem linearMatrix_mulVec_injective {m : ℕ} (L : ComplexVector n →L[ℂ] ComplexVector m)
    (hL : Function.Injective L) : Function.Injective (L17Aux.linearMatrix L).mulVec := by
  intro v w hvw
  apply WithLp.toLp_injective 2
  apply hL
  apply WithLp.ofLp_injective 2
  simpa only [← L17Aux.linearMatrix_mulVec,WithLp.ofLp_toLp] using hvw

end Yau.Proofs.P04Aux
