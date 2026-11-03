import Yau.Proofs.U02PolynomialBounds
import Yau.Proofs.Y02CompositionBounds

/-! Uniform bounds on fixed raw balls for the original polynomial maps.
The degree is their literal maximum component degree. -/

open scoped Topology

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau
open Yau.Proofs.Y02Aux

theorem polynomial_fixed_ball_bound {n : ℕ} (P : PolyMap n) {B : ℝ}
    (hB : 1 ≤ B) {z : ComplexVector n} (hz : ‖z‖ ≤ B) :
    ‖P.eval z‖ ≤ P.coeffNorm * B ^ P.degree := by
  apply (vector_norm_le_sum n (P.eval z)).trans
  rw [PolyMap.coeffNorm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  change ‖MvPolynomial.eval (fun j => z j) (P i)‖ ≤
    (∑ m ∈ (P i).support, ‖(P i).coeff m‖) * B ^ P.degree
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∏ j ∈ m.support, z j ^ m j‖ ≤ ‖z‖ ^ (m.sum fun _ e => e) :=
      monomial_norm_le m z
    _ ≤ B ^ (m.sum fun _ e => e) := pow_le_pow_left₀ (norm_nonneg _) hz _
    _ ≤ B ^ P.degree := pow_le_pow_right₀ hB
      ((MvPolynomial.le_totalDegree hm).trans (component_degree_le P i))

theorem polynomial_fixed_degree_bound {n D : ℕ} (P : PolyMap n) (hD : P.degree ≤ D)
    {B : ℝ} (hB : 1 ≤ B) {z : ComplexVector n} (hz : ‖z‖ ≤ B) :
    ‖P.eval z‖ ≤ P.coeffNorm * B ^ D :=
  (polynomial_fixed_ball_bound P hB hz).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hD) (coeffNorm_nonneg P))

theorem degree_le_natCeil {n : ℕ} {P : PolyMap n} {D : ℝ}
    (hD : (P.degree : ℝ) ≤ D) : P.degree ≤ Nat.ceil D := by
  have hh : (P.degree : ℝ) ≤ (Nat.ceil D : ℝ) := hD.trans (Nat.le_ceil D)
  exact_mod_cast hh

end Yau.NodeProofs.U02Proof
