import Yau.Proofs.C02LinearPrecompositionJets

/-! Local finite jets under an actual affine change of coordinates.
The estimate uses only smoothness on the original open domain. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_comp_affineOn_le
    {O : Set E} (hO : IsOpen O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O)
    (a : E) (s : ℝ) (x : E) (hx : a + s • x ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f (a + s • y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (a + s • x)‖ * |s| ^ m := by
  let V := (fun y : E => a + y) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_const.add continuous_id)
  have hShift : ContDiffOn ℝ ∞ (fun y => f (a + y)) V :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
  have h := norm_iteratedFDeriv_comp_smulOn_le hV hShift s x hx m
  rw [iteratedFDeriv_comp_add_left] at h
  exact h

end Yau.Blueprint.C02Proof
