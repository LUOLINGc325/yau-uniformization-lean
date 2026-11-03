import Yau.Proofs.P04LeviLogChain

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau

/-- Positivity is applied only after the infinite positive numerator has
been obtained; finite vanishing sums need no logarithmic division. -/
theorem leviC_log_posSemidef_of_numerator {n : ℕ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) (hpos : 0 < f z)
    (hnum : ((f z : ℂ) • leviC f z-gradientGram f z).PosSemidef) :
    (leviC (fun y => Real.log (f y)) z).PosSemidef := by
  have H := hnum.smul (inv_nonneg.mpr (sq_nonneg (f z)))
  have hfac : (f z)⁻¹ = ((f z)^2)⁻¹*f z := by
    field_simp
  rw [leviC_log hf hpos,hfac]
  convert H using 1
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_mul]
  ring

end Yau.Proofs.P04Aux
