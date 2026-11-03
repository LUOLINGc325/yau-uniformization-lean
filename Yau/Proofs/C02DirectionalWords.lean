import Yau.Proofs.C02MultilinearBasisBounds

/-! Repeated constant directional derivatives are the actual Fréchet
jet evaluated on the corresponding ordered coordinate tuple. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalWord (b : ι → E) (f : E → F) : List ι → E → F
  | [] => f
  | a :: w => fun x => fderiv ℝ (directionalWord b f w) x (b a)

theorem directionalWord_eq_iteratedFDeriv (b : ι → E) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (w : List ι) (x : E) :
    directionalWord b f w x =
      iteratedFDeriv ℝ w.length f x (fun j => b (w.get j)) := by
  induction w generalizing x with
  | nil => simp only [directionalWord, List.length_nil, iteratedFDeriv_zero_apply]
  | cons a w ih =>
    have hFun : directionalWord b f w =
        fun y => iteratedFDeriv ℝ w.length f y (fun j => b (w.get j)) := funext ih
    rw [directionalWord, hFun]
    have hJet : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) x :=
      (hf.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x
    have h := hJet.iteratedFDeriv_succ_apply_left'
      (m := fun j => b ((a :: w).get j))
    simpa [Fin.tail_def, List.get_eq_getElem] using h.symm

end Yau.Blueprint.C02Proof
