import Yau.Proofs.Y06TriangularInverse
import Yau.Proofs.Y06HomogeneousAlgebra

/-! Uniform finite algebraic bounds for the actual strict triangular inverse. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem polynomial_degree_sub_le (P Q : PolyMap n) :
    (P - Q).degree ≤ max P.degree Q.degree := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  exact (totalDegree_sub (P i) (Q i)).trans
    (max_le_max (component_degree_le P i) (component_degree_le Q i))

theorem nonlinearPart_degree_le (P : PolyMap n) (hd : 1 ≤ d) (hP : P.degree ≤ d) :
    (nonlinearPart P).degree ≤ d :=
  (polynomial_degree_sub_le _ _).trans
    (max_le hP ((linearPoly_degree_le P.linearPart).trans hd))

theorem triangularInverseApprox_degree (P : PolyMap n) (a : Fin n → ℂ)
    (hd : 1 ≤ d) (hP : P.degree ≤ d) (r : ℕ) :
    (triangularInverseApprox P a r).degree ≤ d ^ r := by
  induction r with
  | zero => simp [triangularInverseApprox, PolyMap.degree]
  | succ r ih =>
    apply (comp_degree_le _ _).trans
    apply (Nat.mul_le_mul (linearPoly_degree_le _) (polynomial_degree_sub_le _ _)).trans
    simp only [one_mul]
    apply max_le
    · have hid : (PolyMap.id : PolyMap n).degree ≤ 1 := by
        unfold PolyMap.degree
        apply Finset.sup_le
        intro i hi
        simp [PolyMap.id]
      exact hid.trans (one_le_pow₀ hd)
    · apply (comp_degree_le _ _).trans
      exact (Nat.mul_le_mul (nonlinearPart_degree_le P hd hP) ih).trans_eq (by rw [pow_succ, Nat.mul_comm])

def triangularInverseExponent (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => 4 + d * (triangularInverseExponent d r + 1)

theorem triangularInverseApprox_coeffNorm (P : PolyMap n) (a : Fin n → ℂ)
    (hP : P.degree ≤ d) (hd : 1 ≤ d) {T : ℝ}
    (hT : 2 ≤ T) (hn : (n : ℝ) ≤ T)
    (hN : (nonlinearPart P).coeffNorm ≤ T)
    (hI : (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).coeffNorm ≤ T)
    (r : ℕ) :
    (triangularInverseApprox P a r).coeffNorm ≤ T ^ triangularInverseExponent d r := by
  have hT0 : 0 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  induction r with
  | zero => simp [triangularInverseApprox, PolyMap.coeffNorm, triangularInverseExponent]
  | succ r ih =>
    let e := triangularInverseExponent d r
    have hinner : 1 + (triangularInverseApprox P a r).coeffNorm ≤ T ^ (e + 1) := by
      calc
        _ ≤ 1 + T ^ e := by linarith
        _ ≤ 2 * T ^ e := by have := one_le_pow₀ hT1 (n := e); linarith
        _ ≤ T * T ^ e := mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 _)
        _ = _ := by rw [pow_succ]; ring
    have hcomp : ((nonlinearPart P).comp (triangularInverseApprox P a r)).coeffNorm ≤
        T ^ (1 + d * (e + 1)) := by
      calc
        _ ≤ (nonlinearPart P).coeffNorm *
            (1 + (triangularInverseApprox P a r).coeffNorm) ^ (nonlinearPart P).degree :=
          comp_coeffNorm_le _ _
        _ ≤ T * (T ^ (e + 1)) ^ d := by
          apply mul_le_mul hN
          · exact (pow_le_pow_left₀ (by linarith [coeffNorm_nonneg (triangularInverseApprox P a r)]) hinner _).trans
              (pow_le_pow_right₀ (one_le_pow₀ hT1) (nonlinearPart_degree_le P hd hP))
          · exact pow_nonneg (by linarith [coeffNorm_nonneg (triangularInverseApprox P a r)]) _
          · exact hT0
        _ = _ := by rw [← pow_mul, pow_add, pow_one]; ring_nf
    have hsub : (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r)).coeffNorm ≤
        T ^ (2 + d * (e + 1)) := by
      calc
        _ ≤ (PolyMap.id : PolyMap n).coeffNorm +
            ((nonlinearPart P).comp (triangularInverseApprox P a r)).coeffNorm := coeffNorm_sub_le _ _
        _ ≤ T + T ^ (1 + d * (e + 1)) := by rw [coeffNorm_id]; exact add_le_add hn hcomp
        _ ≤ 2 * T ^ (1 + d * (e + 1)) := by
          have : T ≤ T ^ (1 + d * (e + 1)) :=
            (pow_one T).symm.trans_le (pow_le_pow_right₀ hT1 (by omega))
          linarith
        _ ≤ T * T ^ (1 + d * (e + 1)) :=
          mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 _)
        _ = _ := by rw [← pow_succ']; congr 1; omega
    change ((linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).comp
      (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r))).coeffNorm ≤ _
    calc
      _ ≤ (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).coeffNorm *
          (1 + (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r)).coeffNorm) ^
            (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).degree := comp_coeffNorm_le _ _
      _ ≤ T * (1 + T ^ (2 + d * (e + 1))) := by
        apply mul_le_mul hI
        · exact (pow_le_pow_right₀
            (by linarith [coeffNorm_nonneg (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r))])
            (linearPoly_degree_le _)).trans (by simpa only [pow_one] using add_le_add (le_refl 1) hsub)
        · exact pow_nonneg (by linarith [coeffNorm_nonneg (PolyMap.id - (nonlinearPart P).comp (triangularInverseApprox P a r))]) _
        · exact hT0
      _ ≤ T * (T ^ (3 + d * (e + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hT0
        calc
          _ ≤ 2 * T ^ (2 + d * (e + 1)) := by have := one_le_pow₀ hT1 (n := 2 + d * (e + 1)); linarith
          _ ≤ T * T ^ (2 + d * (e + 1)) := mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 _)
          _ = _ := by rw [← pow_succ']; congr 1; omega
      _ = T ^ (4 + d * (e + 1)) := by rw [← pow_succ']; congr 1; omega
      _ = T ^ triangularInverseExponent d (r + 1) := rfl

end Yau.Proofs.Y06Aux
