import Yau.Proofs.Y05InverseJet

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux

variable {n : ℕ}

def inverseJetExponent (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => d * (inverseJetExponent d m + 1) + 2

theorem polynomial_iteration_bound {B X : ℝ} {e d : ℕ}
    (hB : 2 ≤ B) (hX : 0 ≤ X) (he : X ≤ B ^ e) :
    B + B * (1 + X) ^ d ≤ B ^ (d * (e + 1) + 2) := by
  have hB1 : 1 ≤ B := by linarith
  have hpow : 1 ≤ B ^ e := one_le_pow₀ hB1
  have hbase : 1 + X ≤ B ^ (e + 1) := by
    rw [pow_succ]
    nlinarith
  let q := d * (e + 1)
  have hq : 1 ≤ B ^ q := one_le_pow₀ hB1
  have hfirst : B ≤ B * B ^ q := by
    calc
      B = B * 1 := by ring
      _ ≤ B * B ^ q := mul_le_mul_of_nonneg_left hq (by linarith)
  calc
    _ ≤ B + B * (B ^ (e + 1)) ^ d := by gcongr
    _ = B + B * B ^ q := by dsimp [q]; rw [← pow_mul, Nat.mul_comm]
    _ ≤ B * B ^ q + B * B ^ q := add_le_add hfirst (le_refl _)
    _ = 2 * (B ^ q * B) := by ring
    _ ≤ B * (B ^ q * B) := by gcongr
    _ = B ^ (q + 2) := by rw [pow_add]; ring

theorem inversePicard_coeffNorm_bound {A : PolyMap n} {d : ℕ}
    (hd : 1 ≤ d) (hdeg : A.degree ≤ d) (m : ℕ) :
    (inversePicard A m).coeffNorm ≤
      ((n : ℝ) + 2 + A.coeffNorm) ^ inverseJetExponent d m := by
  let B := (n : ℝ) + 2 + A.coeffNorm
  have hB : 2 ≤ B := by dsimp [B]; linarith [coeffNorm_nonneg A, Nat.cast_nonneg (α := ℝ) n]
  have hR : (A - PolyMap.id).coeffNorm ≤ B := by
    apply (coeffNorm_sub_le A PolyMap.id).trans
    rw [coeffNorm_id]
    dsimp [B]
    linarith
  have hRdeg : (A - PolyMap.id).degree ≤ d := by
    unfold PolyMap.degree
    apply Finset.sup_le
    intro i hi
    apply (totalDegree_sub _ _).trans
    exact max_le ((component_degree_le A i).trans hdeg) (by
      simp only [PolyMap.id, totalDegree_X]; exact hd)
  induction m with
  | zero =>
    simp only [inversePicard, inverseJetExponent, coeffNorm_id, pow_one]
    linarith [coeffNorm_nonneg A]
  | succ m ih =>
    have hQ : 0 ≤ (inversePicard A m).coeffNorm := coeffNorm_nonneg _
    calc
      _ ≤ (PolyMap.id : PolyMap n).coeffNorm +
          ((A - PolyMap.id).comp (inversePicard A m)).coeffNorm := coeffNorm_sub_le _ _
      _ ≤ (n : ℝ) + (A - PolyMap.id).coeffNorm *
          (1 + (inversePicard A m).coeffNorm) ^ (A - PolyMap.id).degree := by
        rw [coeffNorm_id]
        exact add_le_add (le_refl (n : ℝ)) (comp_coeffNorm_le _ _)
      _ ≤ B + B * (1 + (inversePicard A m).coeffNorm) ^ d := by
        have hbase : 1 ≤ 1 + (inversePicard A m).coeffNorm := by linarith
        apply add_le_add
        · dsimp [B]; linarith [coeffNorm_nonneg A]
        · exact mul_le_mul hR (pow_le_pow_right₀ hbase hRdeg)
            (pow_nonneg (by linarith) _) (by linarith)
      _ ≤ _ := polynomial_iteration_bound hB hQ ih

/-- The finite inverse coefficients are polynomially controlled by the
original polynomial's coefficients, with exponent depending only on degree. -/
theorem finiteInverseJet_coeffNorm_bound {A : PolyMap n} {d : ℕ}
    (hd : 1 ≤ d) (hdeg : A.degree ≤ d) :
    (finiteInverseJet A d).coeffNorm ≤
      ((n : ℝ) + 2 + A.coeffNorm) ^ inverseJetExponent d d :=
  (truncate_coeffNorm_le d _).trans (inversePicard_coeffNorm_bound hd hdeg d)

end Yau.Proofs.Y05Aux
