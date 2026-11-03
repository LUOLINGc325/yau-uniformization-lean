import Yau.Proofs.F05TransitionInverse

/-! Actual smooth transitions between two different genuine finite atlases.
The receiving chart can be fixed while exhaustion domains and their
solution atlases change. No physical half-space condition is imposed on
the raw radius-three transition domain. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05CrossTransition (A B : AtlasData M) (i : Fin A.count) (j : Fin B.count) :
    Space n → Space n := fun z => F05Coord B j (lift A i z)

def F05CrossTransitionDomain (A B : AtlasData M) (i : Fin A.count) (j : Fin B.count) :
    Set (Space n) := Metric.ball 0 3 ∩ (lift A i) ⁻¹' (lift B j '' Metric.ball 0 3)

theorem F05_cross_transition_domain_isOpen {O V : Set M.Carrier} {A B : AtlasData M}
    (hA : GenuineAtlas O A) (hB : GenuineAtlas V B) (i : Fin A.count) (j : Fin B.count) :
    IsOpen (F05CrossTransitionDomain A B i j) := by
  have hh := (F05AtlasEquiv hA i).symm.isOpen_inter_preimage
    (F05_lift_ball_isOpen hB j (le_refl 3))
  simpa only [OpenPartialHomeomorph.symm_source,F05AtlasEquiv_target,
    F05AtlasEquiv_inverse,F05CrossTransitionDomain] using hh

theorem F05_cross_transition_lift {V : Set M.Carrier} (A : AtlasData M) {B : AtlasData M}
    (hB : GenuineAtlas V B) (i : Fin A.count) (j : Fin B.count) {z : Space n}
    (hz : z ∈ F05CrossTransitionDomain A B i j) :
    lift B j (F05CrossTransition A B i j z) = lift A i z :=
  F05_lift_coord_image hB j hz.2

theorem F05_cross_transition_contDiffAt {O V : Set M.Carrier} {A B : AtlasData M}
    (hA : GenuineAtlas O A) (hB : GenuineAtlas V B) (i : Fin A.count) (j : Fin B.count)
    {z w : Space n} (hz : z ∈ Metric.ball 0 3) (hw : w ∈ Metric.ball 0 3)
    (heq : lift A i z = lift B j w) :
    ContDiffAt ℝ ∞ (F05CrossTransition A B i j) z := by
  let x := A.center i
  let y := B.center j
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) x).symm
  have hInv : (e : Space n → M.Carrier) = chartInv x := by
    funext q
    simp [e,chartInv,ComplexModel]
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := x))
  have hLeftSource := (hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩
  have hRightSource := (hB.1 j).2.2.2.2.1 ⟨w,hw,rfl⟩
  have hLeftT := (hA.1 i).2.1 hLeftSource
  have hRightT := (hB.1 j).2.1 hRightSource
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
  have hRaw : chartPt y (lift A i z) = B.inverse j w := by
    rw [heq]
    exact (extChartAt (ComplexModel n) y).right_inv hRightT
  have hInverse : ContDiffAt ℝ ∞ (A.inverse i) z :=
    ((hA.1 i).2.2.2.1).contDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hForward : ContDiffAt ℝ ∞ (B.forward j) (chartPt y (lift A i z)) := by
    rw [hRaw]
    exact ((hB.1 j).2.2.1).contDiffAt ((hB.1 j).1.mem_nhds hRightSource)
  have hComposite := hForward.comp z (hChart.comp z hInverse)
  unfold F05CrossTransition F05Coord lift
  exact hComposite

end Yau.Proofs.F05Aux
