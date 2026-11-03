import Yau.Proofs.F04ClosedParabolicGradient
import Yau.Proofs.F04SmoothOperatorLinearity
import Yau.LeafProofs.L16WordSource

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- The true spatial partial derivative remains smooth on the same time
 set, with an arbitrary normed real target (in particular a first-jet
 space). No time extension or unproved higher-jet bound is used. -/
theorem joint_spatial_fderivWithin_smooth_range
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set (Space n)} {I : Set ℝ} (hO : UniqueDiffOn ℝ O)
    {u : Point n → F} (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p => fderivWithin ℝ (fun z => u (z,p.2)) O p.1) (O ×ˢ I) := by
  let Q := O ×ˢ I
  have hJoint : ContDiffOn ℝ ∞ (fun q : Point n × Space n => u (q.2,q.1.2)) (Q ×ˢ O) :=
    hu.comp (contDiffOn_snd.prodMk contDiffOn_fst.snd) (fun q hq => ⟨hq.2,hq.1.2⟩)
  intro p hp
  have hJ : ContDiffWithinAt ℝ ∞
      (Function.uncurry (fun (q : Point n) (z : Space n) => u (z,q.2))) (Q ×ˢ O) (p,p.1) := by
    change ContDiffWithinAt ℝ ∞ (fun q : Point n × Space n => u (q.2,q.1.2)) (Q ×ˢ O) (p,p.1)
    exact hJoint (p,p.1) ⟨hp,hp.1⟩
  exact hJ.fderivWithin (m := ∞) contDiffWithinAt_fst hO (by simp) hp (fun q hq => hq.1)

theorem open_spatialD_smooth {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {I : Set ℝ} {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) :
    ContDiffOn ℝ ∞ (spatialD u) (O ×ˢ I) := by
  apply (joint_spatial_fderivWithin_smooth hO.uniqueDiffOn hu).congr
  intro p hp
  exact (fderivWithin_of_isOpen hO hp.1).symm

theorem open_spatialDD_smooth {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {I : Set ℝ} {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) :
    ContDiffOn ℝ ∞ (spatialDD u) (O ×ˢ I) := by
  apply (joint_spatial_fderivWithin_smooth_range hO.uniqueDiffOn (open_spatialD_smooth hO hu)).congr
  intro p hp
  exact (fderivWithin_of_isOpen hO hp.1).symm

/-- The actual nondivergence operator of a genuinely closed-slab smooth
 function is continuous on that SAME closed slab, including its true
 one-sided time derivative. -/
theorem linearOp_continuousOn_closed_slab
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {T : ℝ} (hT : 0 < T)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 T) a b)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T)) :
    ContinuousOn (linearOp (O ×ˢ Icc 0 T) a b u) (O ×ˢ Icc 0 T) := by
  have hTime := Yau.Proofs.F05Aux.F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hT) hu
  have hTC : ContinuousOn (timeD (O ×ˢ Icc 0 T) u) (O ×ˢ Icc 0 T) := by
    apply hTime.continuousOn.congr
    intro p hp
    have hFiber : {t : ℝ | (p.1,t) ∈ O ×ˢ Icc 0 T} = Icc 0 T := by ext t; simp [hp.1]
    simp only [timeD,hFiber]
  have hD := open_spatialD_smooth hO hu
  have hDD := open_spatialDD_smooth hO hu
  unfold linearOp
  apply ContinuousOn.sub
  · apply hTC.sub
    apply continuousOn_finsetSum Finset.univ
    intro i _
    apply continuousOn_finsetSum Finset.univ
    intro j _
    exact ((matrixEntryCLM i j).continuous.comp_continuousOn hSmooth.1.continuousOn).mul
      ((hDD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).continuousOn
  · apply continuousOn_finsetSum Finset.univ
    intro i _
    exact (hSmooth.2 i).continuousOn.mul (hD.clm_apply contDiffOn_const).continuousOn

end Yau.F04Proof
