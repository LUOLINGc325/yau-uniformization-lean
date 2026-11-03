import Yau.Blueprint.ParabolicSpaces
import Mathlib

/-! The actual one-sided partial time derivative of a smooth cylinder field
is smooth on the same closed time set when derivatives are unique there. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic

theorem F05_joint_time_derivative_smooth {n : ℕ} {U : Set (Space n)} {I : Set ℝ}
    (hI : UniqueDiffOn ℝ I) {f : Point n → ℝ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ I)) :
    ContDiffOn ℝ ∞ (fun p => derivWithin (fun t => f (p.1,t)) I p.2) (U ×ˢ I) := by
  let Q := U ×ˢ I
  have hJoint : ContDiffOn ℝ ∞ (fun q : Point n × ℝ => f (q.1.1,q.2)) (Q ×ˢ I) :=
    hf.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun q hq => ⟨hq.1.1,hq.2⟩)
  have hWithin : ContDiffOn ℝ ∞
      (fun p : Point n => fderivWithin ℝ (fun t => f (p.1,t)) I p.2) Q := by
    intro p hp
    have hJ : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : Point n) (t : ℝ) => f (q.1,t))) (Q ×ˢ I) (p,p.2) := by
      have hEq : Function.uncurry (fun (q : Point n) (t : ℝ) => f (q.1,t)) =
          (fun q : Point n × ℝ => f (q.1.1,q.2)) := rfl
      rw [hEq]
      exact hJoint (p,p.2) ⟨hp,hp.2⟩
    exact hJ.fderivWithin (m := ∞) contDiffWithinAt_snd hI (by simp) hp (fun q hq => hq.2)
  simpa only [derivWithin] using hWithin.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Point n => (1 : ℝ)) Q)

end Yau.Proofs.F05Aux
