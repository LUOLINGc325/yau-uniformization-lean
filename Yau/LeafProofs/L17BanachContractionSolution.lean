import Yau.LeafProofs.L17BanachContractionBounds

open Set Metric
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachContractionAux

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace X]

variable (e : X ≃L[ℝ] Y) (f : Y) (N : X → Y) (r L : ℝ)
    (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    (hZero : ‖e.symm (f+N 0)‖ ≤ r/2)

include hr hLip hSmall hZero in
theorem exists_unique_ball_solution : ∃! u : X, ‖u‖ ≤ r ∧ e u=f+N u := by
  let hs := iterationMap_mapsTo e f N hr hLip hSmall hZero
  let F := hs.restrict (iterationMap e f N) (closedBall 0 r) (closedBall 0 r)
  letI : CompleteSpace ↥(closedBall (0 : X) r) := isClosed_closedBall.isComplete.completeSpace_coe
  letI : Nonempty ↥(closedBall (0 : X) r) := ⟨⟨0,by simpa using hr⟩⟩
  have hContr : ContractingWith (1/2 : ℝ≥0) F :=
    ⟨by norm_num,(iterationMap_lipschitzOn e f N hLip hSmall).mapsToRestrict hs⟩
  let u := hContr.fixedPoint F
  have hfix : iterationMap e f N (u : X)=(u : X) := congrArg Subtype.val hContr.fixedPoint_isFixedPt
  have hu : ‖(u : X)‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using u.property
  have heq : e (u : X)=f+N (u : X) := (equation_iff_fixed e f N _).mpr hfix
  refine ⟨u,⟨hu,heq⟩,?_⟩
  intro v hv
  exact ball_equation_unique e f N hLip hSmall hv.1 hu hv.2 heq

def ballSolution : X :=
  Classical.choose (exists_unique_ball_solution e f N r L hr hLip hSmall hZero)

theorem ballSolution_mem : ‖ballSolution e f N r L hr hLip hSmall hZero‖ ≤ r :=
  (Classical.choose_spec (exists_unique_ball_solution e f N r L hr hLip hSmall hZero)).1.1

theorem ballSolution_equation :
    e (ballSolution e f N r L hr hLip hSmall hZero)=f+N (ballSolution e f N r L hr hLip hSmall hZero) :=
  (Classical.choose_spec (exists_unique_ball_solution e f N r L hr hLip hSmall hZero)).1.2

theorem ballSolution_norm_le :
    ‖ballSolution e f N r L hr hLip hSmall hZero‖ ≤ 2*‖e.symm (f+N 0)‖ :=
  ball_equation_norm_le e f N hr hLip hSmall
    (ballSolution_mem e f N r L hr hLip hSmall hZero)
    (ballSolution_equation e f N r L hr hLip hSmall hZero)

theorem ballSolution_unique {u : X} (hu : ‖u‖ ≤ r) (heq : e u=f+N u) :
    u=ballSolution e f N r L hr hLip hSmall hZero :=
  ball_equation_unique e f N hLip hSmall hu
    (ballSolution_mem e f N r L hr hLip hSmall hZero) heq
    (ballSolution_equation e f N r L hr hLip hSmall hZero)

include hr hLip hSmall hZero in
theorem exists_unique_ball_solution_norm :
    ∃ u : X, ‖u‖ ≤ r ∧ e u=f+N u ∧ ‖u‖ ≤ 2*‖e.symm (f+N 0)‖ ∧
      ∀ v : X, ‖v‖ ≤ r → e v=f+N v → v=u := by
  refine ⟨ballSolution e f N r L hr hLip hSmall hZero,
    ballSolution_mem e f N r L hr hLip hSmall hZero,
    ballSolution_equation e f N r L hr hLip hSmall hZero,
    ballSolution_norm_le e f N r L hr hLip hSmall hZero,?_⟩
  exact fun v hv heq => ballSolution_unique e f N r L hr hLip hSmall hZero hv heq

end Yau.LeafProofs.L17BanachContractionAux
