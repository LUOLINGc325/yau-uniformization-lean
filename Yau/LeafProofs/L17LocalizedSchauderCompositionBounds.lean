import Yau.LeafProofs.L17LocalizedSchauderBilinearDifference
import Yau.LeafProofs.L17TaylorCompositionBounds

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_zero_function (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (fun _ : E => (0 : F)) x = 0 := by
  cases k with
  | zero => ext m; rfl
  | succ k => rw [← iteratedFDerivWithin_univ,iteratedFDerivWithin_succ_const]; rfl

/-- Actual finite-order composition bounds remain linear in the outer
jet amplitude. No derivative beyond k is required. -/
theorem norm_iteratedFDeriv_comp_le_linear (k : ℕ) {f : E → F} {g : F → G} {x : E}
    (hg : ContDiffAt ℝ (k : ℕ∞ω) g (f x)) (hf : ContDiffAt ℝ (k : ℕ∞ω) f x)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hOuter : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A)
    (hInner : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ taylorOuterDifferenceConstant k D*A := by
  have h := norm_iteratedFDeriv_comp_sub_le k hg (contDiffAt_const (c := (0 : G))) hf hf
    hA hA hD (le_refl (0 : ℝ)) hOuter
    (fun j hj => by simpa only [iteratedFDeriv_zero_function,sub_zero] using hOuter j hj)
    hInner hInner (fun j hj => by simp only [sub_self,norm_zero,le_refl])
  have hz : (fun _ : F => (0 : G)) ∘ f = (fun _ => (0 : G)) := rfl
  simpa only [hz,iteratedFDeriv_zero_function,sub_zero,mul_zero,add_zero,zero_add] using h

end Yau.LeafProofs.L17LocalizedSchauderAux
