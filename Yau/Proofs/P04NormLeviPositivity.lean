import Yau.Proofs.P04LeviLogChain
import Yau.LeafProofs.L22Second
import Yau.LeafProofs.L22LeviBasic

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem leviC_posSemidef_of_localMin {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hmin : IsLocalMin f z) : (leviC f z).PosSemidef := by
  apply (L22Aux.leviC_posSemidef_iff hf).mpr
  intro v
  exact div_nonneg (add_nonneg (L22Aux.hessian_nonneg_of_localMin hf hmin v)
    (L22Aux.hessian_nonneg_of_localMin hf hmin (Complex.I • v))) (by norm_num)

/-- The exact logarithm chain rule recovers norm positivity wherever the
norm is positive. No logarithm is used at a zero of the norm. -/
theorem leviC_posSemidef_of_log {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hpos : 0 < f z)
    (hlog : (leviC (fun y => Real.log (f y)) z).PosSemidef) :
    (leviC f z).PosSemidef := by
  have heq : (((f z)⁻¹ : ℝ) : ℂ) • leviC f z =
      leviC (fun y => Real.log (f y)) z+
        ((((f z)^2)⁻¹ : ℝ) : ℂ) • gradientGram f z := by
    rw [leviC_log hf hpos]
    abel
  have hscaled : ((((f z)⁻¹ : ℝ) : ℂ) • leviC f z).PosSemidef := by
    rw [heq]
    exact hlog.add ((gradientGram_posSemidef f z).smul
      (Complex.zero_le_real.mpr (inv_nonneg.mpr (sq_nonneg _))))
  have H := hscaled.smul (Complex.zero_le_real.mpr hpos.le)
  simpa only [smul_smul,Complex.ofReal_inv,mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr hpos.ne'),one_smul] using H

end Yau.Proofs.P04Aux
