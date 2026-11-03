import Yau.Proofs.F01LogDetOrder
import Yau.Proofs.F01NativeLogDetEvolution
import Yau.Proofs.F01ClosedTimeBounds

/-! The original finite metric sandwich itself bounds the actual
logarithmic determinant ratio and, through the actual one-sided scalar PDE,
the potential. No spatial derivative bound is inferred from smoothness. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem logdet_ratio_abs_bound_of_sandwich {H K : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hK : K.PosDef) {C : ℝ} (hC1 : 1 ≤ C)
    (hlo : (K - ((C⁻¹ : ℝ) : ℂ) • H).PosSemidef)
    (hhi : ((C : ℂ) • H - K).PosSemidef) :
    |Real.log (K.det.re / H.det.re)| ≤ (n : ℝ) * Real.log C := by
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hreverse : ((C : ℂ) • K - H).PosSemidef := by
    have hscalar : (0 : ℂ) ≤ (C : ℂ) := Complex.nonneg_iff.mpr ⟨hC.le, by simp⟩
    have hh := hlo.smul hscalar
    simpa only [smul_sub, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hc, one_smul] using hh
  have hupper := logdet_ratio_upper_of_order hH hK hC hhi
  have hlower := logdet_ratio_upper_of_order hK hH hC hreverse
  have hHp := (Complex.pos_iff.mp hH.det_pos).1
  have hKp := (Complex.pos_iff.mp hK.det_pos).1
  rw [Real.log_div hHp.ne' hKp.ne'] at hlower
  rw [Real.log_div hKp.ne' hHp.ne'] at hupper ⊢
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem closed_potential_abs_bound_of_time_value {U P : ℝ → ℝ} {T A : ℝ}
    (hT : 0 ≤ T) (hU0 : U 0 = 0)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U (P t) (Icc 0 T) t)
    (hP : ∀ t ∈ Icc 0 T, |P t| ≤ A) :
    ∀ t ∈ Icc 0 T, |U t| ≤ A * t := by
  have hupper := linear_upper_of_closed_derivative_cap hT hU
    (fun t ht => (le_abs_self (P t)).trans (hP t ht))
  have hlower := linear_upper_of_closed_derivative_cap hT
    (fun t ht => (hU t ht).neg) (fun t ht => (neg_le_abs (P t)).trans (hP t ht))
  intro t ht
  have hu := hupper t ht
  have hl := hlower t ht
  change -U t ≤ -U 0 + A * t at hl
  simp only [hU0, neg_zero, zero_add] at hu hl
  exact abs_le.mpr ⟨by linarith, hu⟩

end Yau.NodeProofs.F01Aux
