import Yau.Proofs.F05SmoothTimeJets

open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic

/-- Actual spatial fiber derivatives vary smoothly on the same time set,
 including a closed time face. Unique spatial derivatives suffice; no
 smooth extension of the original field to negative time is assumed. -/
theorem joint_spatial_fderivWithin_smooth
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ} (hO : UniqueDiffOn ℝ O)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) :
    ContDiffOn ℝ ∞
      (fun p => fderivWithin ℝ (fun z => u (z, p.2)) O p.1) (O ×ˢ I) := by
  let Q := O ×ˢ I
  have hJoint : ContDiffOn ℝ ∞ (fun q : Point n × Space n => u (q.2, q.1.2)) (Q ×ˢ O) :=
    hu.comp (contDiffOn_snd.prodMk contDiffOn_fst.snd) (fun q hq => ⟨hq.2, hq.1.2⟩)
  intro p hp
  have hJ : ContDiffWithinAt ℝ ∞
      (Function.uncurry (fun (q : Point n) (z : Space n) => u (z, q.2))) (Q ×ˢ O) (p, p.1) := by
    change ContDiffWithinAt ℝ ∞ (fun q : Point n × Space n => u (q.2, q.1.2)) (Q ×ˢ O) (p, p.1)
    exact hJoint (p, p.1) ⟨hp, hp.1⟩
  exact hJ.fderivWithin (m := ∞) contDiffWithinAt_fst hO (by simp) hp (fun q hq => hq.1)

/-- A full-space field smooth on a closed time slab has its ACTUAL spatial
 differential smooth on that same slab, not just on positive-time interiors. -/
theorem fullSpace_spatialD_smooth
    {n : ℕ} {I : Set ℝ} {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ I)) :
    ContDiffOn ℝ ∞ (spatialD u) (univ ×ˢ I) := by
  have hh := joint_spatial_fderivWithin_smooth uniqueDiffOn_univ hu
  apply hh.congr
  intro p _hp
  simp only [spatialD, fderivWithin_univ]

theorem fullSpace_spatialComponent_smooth
    {n : ℕ} {I : Set ℝ} {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ I)) (i : RIdx n) :
    ContDiffOn ℝ ∞ (fun p => spatialD u p (realVec i)) (univ ×ˢ I) :=
  (fullSpace_spatialD_smooth hu).clm_apply contDiffOn_const

end Yau.F04Proof
