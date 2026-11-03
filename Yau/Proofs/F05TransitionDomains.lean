import Yau.Proofs.F05Transitions
import Yau.Proofs.F05AtlasHomeomorph

/-! Actual open transition domains, including points beyond the physical
halfspace. They are used only where a genuine supported chart factor lives. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05TransitionDomain (A : AtlasData M) (i j : Fin A.count) : Set (Space n) :=
  Metric.ball 0 3 ∩ (lift A i) ⁻¹' (lift A j '' Metric.ball 0 3)

theorem F05TransitionDomain_isOpen {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) : IsOpen (F05TransitionDomain A i j) := by
  have hh := (F05AtlasEquiv hA i).symm.isOpen_inter_preimage
    (F05_lift_ball_isOpen hA j (le_refl 3))
  simpa only [OpenPartialHomeomorph.symm_source,F05AtlasEquiv_target,
    F05AtlasEquiv_inverse,F05TransitionDomain] using hh

theorem F05Transition_contDiffAt_of_lifts {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {z w : Space n}
    (hz : z ∈ Metric.ball 0 3) (hw : w ∈ Metric.ball 0 3)
    (heq : lift A i z = lift A j w) : ContDiffAt ℝ ∞ (F05Transition A i j) z := by
  let x := A.center i
  let y := A.center j
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) x).symm
  have hInv : (e : Space n → M.Carrier) = chartInv x := by
    funext q
    simp [e,chartInv,ComplexModel]
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := x))
  have hLeftSource := (hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩
  have hRightSource := (hA.1 j).2.2.2.2.1 ⟨w,hw,rfl⟩
  have hLeftT := (hA.1 i).2.1 hLeftSource
  have hRightT := (hA.1 j).2.1 hRightSource
  have hCross : lift A i z ∈ (extChartAt (ComplexModel n) y).source := by
    rw [heq]
    exact (extChartAt (ComplexModel n) y).map_target hRightT
  have hMem : A.inverse i z ∈ forwardChartDomain e y := by
    refine ⟨?_,?_⟩
    · simpa [e,chartTarget,ComplexModel] using hLeftT
    · rw [hInv]
      exact hCross
  have hChart : ContDiffAt ℝ ∞ (fun q => chartPt y (chartInv x q)) (A.inverse i z) := by
    have hh := (forwardChart_real_contDiffOn e he y).contDiffAt
      ((forwardChartDomain_isOpen e y).mem_nhds hMem)
    rwa [hInv] at hh
  have hRaw : chartPt y (lift A i z) = A.inverse j w := by
    rw [heq]
    exact (extChartAt (ComplexModel n) y).right_inv hRightT
  have hInverse : ContDiffAt ℝ ∞ (A.inverse i) z :=
    ((hA.1 i).2.2.2.1).contDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hForward : ContDiffAt ℝ ∞ (A.forward j) (chartPt y (lift A i z)) := by
    rw [hRaw]
    exact ((hA.1 j).2.2.1).contDiffAt ((hA.1 j).1.mem_nhds hRightSource)
  have hComposite := hForward.comp z (hChart.comp z hInverse)
  unfold F05Transition F05Coord lift
  exact hComposite

theorem F05Transition_contDiffOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) :
    ContDiffOn ℝ ∞ (F05Transition A i j) (F05TransitionDomain A i j) := by
  intro z hz
  obtain ⟨w,hw,heq⟩ := hz.2
  exact (F05Transition_contDiffAt_of_lifts hA i j hz.1 hw heq.symm).contDiffWithinAt

end Yau.Proofs.F05Aux
