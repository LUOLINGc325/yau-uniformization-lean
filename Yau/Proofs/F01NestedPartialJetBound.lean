import Yau.Proofs.F01PartialJetBound

/-! Coordinate jets in the nested parameters (center,scale,coordinate).
The two affine restrictions control actual derivatives, without a choice of
Taylor series for the sliced map. -/
open Set
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {A B E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_fixedTwo_le {W : Set (A × B × E)} (hW : IsOpen W)
    {f : A × B × E → F} (hf : ContDiffOn ℝ ∞ f W) (a : A) (b : B) {z : E}
    (hz : (a, b, z) ∈ W) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => f (a, b, w)) z‖ ≤ ‖iteratedFDeriv ℝ k f (a, b, z)‖ := by
  let V := (fixedFirstInclusion (E := B × E) a) ⁻¹' W
  have hV : IsOpen V := hW.preimage (fixedFirstInclusion a).continuous
  have ha : ContDiff ℝ ∞ (fun w : B × E => (a, w)) := by fun_prop
  have hfV : ContDiffOn ℝ ∞ (fun w : B × E => f (a, w)) V :=
    hf.comp ha.contDiffOn (fun _ h => h)
  exact (norm_iteratedFDeriv_fixedFirst_le hV hfV b hz k).trans
    (norm_iteratedFDeriv_fixedFirst_le hW hf a hz k)

end Yau.NodeProofs.F01Aux
