import Yau.Proofs.F01RealifiedOrder

/-! Relative Hermitian bounds and actual background chart bounds combine
into the precise real transformed-matrix sandwich used by L05. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem relative_scalar_matrix_sandwich
    {H K : Matrix (Fin n) (Fin n) ℂ} {ell upper c C : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hHlo : (H - (ell : ℂ) • 1).PosSemidef)
    (hHhi : ((upper : ℂ) • 1 - H).PosSemidef)
    (hKlo : (K - (c : ℂ) • H).PosSemidef)
    (hKhi : ((C : ℂ) • H - K).PosSemidef) :
    (K - ((c * ell : ℝ) : ℂ) • 1).PosSemidef ∧
      ((((C * upper : ℝ) : ℂ) • 1) - K).PosSemidef := by
  constructor
  · have hp := hKlo.add (hHlo.smul (Complex.zero_le_real.mpr hc))
    convert hp using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
    ring
  · have hp := hKhi.add (hHhi.smul (Complex.zero_le_real.mpr hC))
    convert hp using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
    ring

theorem iota_scalar_matrix_sandwich
    {K : Matrix (Fin n) (Fin n) ℂ} {ell upper : ℝ}
    (hlo : (K - (ell : ℂ) • 1).PosSemidef)
    (hhi : ((upper : ℂ) • 1 - K).PosSemidef) :
    ((iota K : Mat n) - ell • (1 : Mat n)).PosSemidef ∧
      (upper • (1 : Mat n) - (iota K : Mat n)).PosSemidef := by
  have hlower := iota_lower_order hlo
  have hupper := iota_upper_order hhi
  rw [iota_one_matrix] at hlower hupper
  exact ⟨hlower, hupper⟩

end Yau.NodeProofs.F01Aux
