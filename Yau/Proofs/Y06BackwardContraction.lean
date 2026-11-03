import Yau.Proofs.Y06LinearNorm
import Yau.Proofs.Y06ScalarExponent

/-! The complete homogeneous backward operator has the paper's diagonal
decay before the polynomial jump-conjugation factor is estimated. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment

variable {n m : ℕ}

theorem backwardOperator_clock_bound (a μ : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (J : Herm n) (w : Fin n → ℝ) {P : PolyMap n} (hP : Homogeneous P m)
    {τ Δs Q A κ ch s j : ℝ} (hτ : 0 < τ) (hA : 0 < A) (hκ : 0 ≤ κ) (hj : 0 < j)
    (hμ : ∀ i, μ i = -2 * Real.log (a i) / τ)
    (htrace : τ * (∑ l, μ l) = Δs) (hupper : (∑ l, μ l) ≤ A * Q)
    (hlower : ch * Real.sqrt s ≤ Δs)
    (hgap : ∀ i (β : Fin n →₀ ℕ), β.sum (fun _ e => e) = m →
      w i < ∑ l, (β l : ℝ) * w l → κ * Q / j ^ 2 ≤ (∑ l, (β l : ℝ) * μ l) - μ i) :
    (backwardOperator (Matrix.diagonal (fun i => (a i : ℂ))) J w P).coeffNorm ≤
      (Real.exp (-(κ * ch / (2 * A)) * Real.sqrt s / j ^ 2) *
        (∑ i, ∑ l, ‖J⁻¹ i l‖) * (1 + (linearPolynomial J).coeffNorm) ^ m) * P.coeffNorm := by
  apply backwardOperator_coeffNorm_bound (fun i => (a i : ℂ))
    (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (ha i))) J w hP (Real.exp_pos _).le
  intro i β hdegree hforbidden
  have hscalar := diagonal_factor_clock_bound a μ ha hτ hA hκ hj hμ htrace hupper hlower
    i β (hgap i β hdegree hforbidden)
  simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha _)] using hscalar

theorem jump_factor_macro_bound {j A B S T : ℝ} (hj : 0 ≤ j)
    (hT0 : 0 ≤ T) (hS : S ≤ (1 + j) ^ A) (hT : T ≤ (1 + j) ^ B) (m : ℕ) :
    S * T ^ m ≤ (1 + j) ^ (A + B * m) := by
  have hbase : 0 < 1 + j := by linarith
  calc
    _ ≤ (1 + j) ^ A * ((1 + j) ^ B) ^ m :=
      mul_le_mul hS (pow_le_pow_left₀ hT0 hT m) (pow_nonneg hT0 m) (Real.rpow_pos_of_pos hbase A).le
    _ = (1 + j) ^ A * (1 + j) ^ (B * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    _ = _ := (Real.rpow_add hbase A (B * m)).symm

end Yau.Proofs.Y06Aux
