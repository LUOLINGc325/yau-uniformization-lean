import Mathlib

/-! Constant amplitude and the same affine physical clock give the exact next scaling weight. -/
noncomputable section
namespace Yau.Proofs.C05NormalizedScalarTimeEvolutionAux

theorem hasDerivAt_div_pow_comp_clock {f : ℝ → ℝ} {D : ℝ}
    (R t0 z : ℝ) (hR : 0 < R) (p : ℕ)
    (hf : HasDerivAt f D (t0 + z / R)) :
    HasDerivAt (fun w => f (t0 + w / R) / R ^ p) (D / R ^ (p+1)) z := by
  have hc : HasDerivAt (fun w : ℝ => t0 + w / R) (1 / R) z :=
    ((hasDerivAt_id z).div_const R).const_add t0
  have H := (hf.comp z hc).div_const (R ^ p)
  dsimp only [Function.comp_def] at H
  convert H using 1 <;> field_simp [hR.ne', pow_succ] <;> ring

end Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
