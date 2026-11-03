import Yau.Proofs.F01ScalarLeviDiagonal

/-! The actual exponential Hessian and its finite diagonal trace error.
The constants are the previously controlled Levi and gradient budgets. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem leviC_exp_diagonal {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (i : Fin n) :
    (leviC (fun w => Real.exp (f w)) z i i).re =
      Real.exp (f z) * ((leviC f z i i).re +
        Complex.normSq (wirt (fun w => (f w : ℂ)) z (stdVec i))) := by
  rw [scalar_levi_diagonal_comp hf Real.contDiff_exp.contDiffAt,
    Real.deriv_exp, Real.deriv_exp]
  ring

theorem conformal_second_exchange_trace_bound
    (weights F D : Fin n → ℝ) (hw : ∀ i, 0 ≤ weights i)
    {E q B G : ℝ} (hE : 0 < E) (hq : E ≤ q) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hF : ∀ i, |F i| ≤ B * E)
    (hD0 : ∀ i, 0 ≤ D i) (hD : ∀ i, D i ≤ G * E) (a : Fin n) :
    q⁻¹ * (∑ i, weights i * (E * (F a + D a) - E * (F i + D i))) +
        (∑ i, weights i * F i) ≤ (3 * B + G) * E * ∑ i, weights i := by
  have hqp : 0 < q := lt_of_lt_of_le hE hq
  have hlocal (i : Fin n) :
      q⁻¹ * (E * (F a + D a) - E * (F i + D i)) + F i ≤ (3 * B + G) * E := by
    have hfa := abs_le.mp (hF a)
    have hfi := abs_le.mp (hF i)
    have hR : E * (F a + D a) - E * (F i + D i) ≤ E ^ 2 * (2 * B + G) := by
      have h1 := mul_le_mul_of_nonneg_left hfa.2 hE.le
      have h2 := mul_le_mul_of_nonneg_left hfi.1 hE.le
      have h3 := mul_le_mul_of_nonneg_left (hD a) hE.le
      have h4 := mul_nonneg hE.le (hD0 i)
      nlinarith
    have htarget : E ^ 2 * (2 * B + G) ≤ (E * (2 * B + G)) * q := by
      have hh := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ E * (2 * B + G))
      nlinarith
    have hdiv : (E * (F a + D a) - E * (F i + D i)) / q ≤ E * (2 * B + G) :=
      (div_le_iff₀ hqp).mpr (hR.trans htarget)
    rw [div_eq_mul_inv] at hdiv
    nlinarith
  calc
    _ = ∑ i, weights i *
        (q⁻¹ * (E * (F a + D a) - E * (F i + D i)) + F i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, weights i * ((3 * B + G) * E) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlocal i) (hw i))
    _ = _ := by rw [← Finset.sum_mul]; ring

end Yau.NodeProofs.F01Aux
