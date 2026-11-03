import Yau.Blueprint.ParabolicSpaces
import Mathlib

/-! Smoothness of actual spatial jets remains valid at a closed time face.
Only the spatial set is required to be open. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_joint_spatial_derivative_smooth {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Set (Space n)} {I : Set ℝ}
    (hU : IsOpen U) {f : Point n → V} (hf : ContDiffOn ℝ ∞ f (U ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun z => f (z,p.2)) p.1) (U ×ˢ I) := by
  let Q := U ×ˢ I
  have hJoint : ContDiffOn ℝ ∞ (fun q : Point n × Space n => f (q.2,q.1.2)) (Q ×ˢ U) :=
    hf.comp (contDiffOn_snd.prodMk contDiffOn_fst.snd) (fun q hq => ⟨hq.2,hq.1.2⟩)
  have hWithin : ContDiffOn ℝ ∞
      (fun p : Point n => fderivWithin ℝ (fun z => f (z,p.2)) U p.1) Q := by
    intro p hp
    have hJ : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : Point n) (z : Space n) => f (z,q.2)))
        (Q ×ˢ U) (p,p.1) := by
      have hEq : Function.uncurry (fun (q : Point n) (z : Space n) => f (z,q.2)) =
          (fun q : Point n × Space n => f (q.2,q.1.2)) := rfl
      rw [hEq]
      exact hJoint (p,p.1) ⟨hp,hp.1⟩
    exact hJ.fderivWithin (m := ∞) contDiffWithinAt_fst hU.uniqueDiffOn (by simp) hp (fun q hq => hq.1)
  apply hWithin.congr
  intro p hp
  exact (fderivWithin_of_isOpen hU hp.1).symm

theorem F05_joint_spatial_jets_smooth {n : ℕ} {U : Set (Space n)} {I : Set ℝ}
    (hU : IsOpen U) {f : Point n → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ I)) :
    ContDiffOn ℝ ∞ (spatialD f) (U ×ˢ I) ∧ ContDiffOn ℝ ∞ (spatialDD f) (U ×ˢ I) := by
  have hFirst := F05_joint_spatial_derivative_smooth hU hf
  exact ⟨hFirst,F05_joint_spatial_derivative_smooth hU hFirst⟩

end Yau.Proofs.F05Aux
