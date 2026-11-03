import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Hermitian

/-! Same-matrix Cauchy--Schwarz in the actual complex Hermitian pairing. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.LogDual

theorem positive_matrix_cauchy {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℂ) (hK : K.PosDef) (xi c : ι → ℂ) :
    ‖star xi ⬝ᵥ (K *ᵥ c)‖ ^ 2 ≤
      (star xi ⬝ᵥ (K *ᵥ xi)).re * (star c ⬝ᵥ (K *ᵥ c)).re := by
  have hh := hK.star_dotProduct_mulVec_mul_le xi c
  have hr := (Complex.le_def.mp hh).1
  have hx := hK.isHermitian.im_star_dotProduct_mulVec_self xi
  have hc := hK.isHermitian.im_star_dotProduct_mulVec_self c
  change (star xi ⬝ᵥ (K *ᵥ xi)).im = 0 at hx
  change (star c ⬝ᵥ (K *ᵥ c)).im = 0 at hc
  have hn : ‖star xi ⬝ᵥ (K *ᵥ c)‖ ^ 2 =
      (star xi ⬝ᵥ (K *ᵥ c)).re * (star xi ⬝ᵥ (K *ᵥ c)).re +
        (star xi ⬝ᵥ (K *ᵥ c)).im * (star xi ⬝ᵥ (K *ᵥ c)).im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hn]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    hx, hc, mul_zero, sub_zero] at hr
  nlinarith

end Yau.Proofs.C03Aux.LogDual
