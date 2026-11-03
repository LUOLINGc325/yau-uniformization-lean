import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Yau.Proofs.Y02Homogeneous

/-! A homogeneous divergence-free field is a sum of elementary curls. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

/-- The elementary two-coordinate curl of a scalar polynomial. -/
def curl (i j : Fin n) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] PolyMap n :=
  (LinearMap.single ℂ (fun _ : Fin n => MvPolynomial (Fin n) ℂ) i).comp
      (pderiv j).toLinearMap -
    (LinearMap.single ℂ (fun _ : Fin n => MvPolynomial (Fin n) ℂ) j).comp
      (pderiv i).toLinearMap

theorem curl_apply (i j : Fin n) (H : MvPolynomial (Fin n) ℂ) (k : Fin n) :
    curl i j H k = (Pi.single i (pderiv j H) : PolyMap n) k -
      (Pi.single j (pderiv i H) : PolyMap n) k := rfl

theorem sum_curl_apply (H : Fin n → Fin n → MvPolynomial (Fin n) ℂ) (k : Fin n) :
    (∑ i, ∑ j, curl i j (H i j)) k =
      (∑ j, pderiv j (H k j)) - ∑ i, pderiv i (H i k) := by
  classical
  simp only [Finset.sum_apply, curl_apply, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    simp [Pi.single_apply]
  · simp [Pi.single_apply]

theorem sum_pderiv_X_mul (P : PolyMap n) (k : Fin n) :
    (∑ i, pderiv i (X k * P i)) = P k + X k * divergence n P := by
  classical
  simp only [pderiv_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  congr 1
  simp [pderiv_X, Pi.single_apply]

theorem homogeneous_sum_pderiv_X_mul {m : ℕ} (P : PolyMap n)
    (hP : P ∈ homogeneousFields n m) (k : Fin n) :
    (∑ j, pderiv j (X j * P k)) = (n + m) • P k := by
  simp only [pderiv_mul, pderiv_X_self, one_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [(hP k).sum_X_mul_pderiv, add_nsmul]

/-- Euler's identity gives a polynomial potential with a fixed denominator. -/
theorem homogeneous_sum_curl {m : ℕ} (hm : 1 ≤ m) (P : PolyMap n)
    (hP : P ∈ homogeneousFields n m) :
    (∑ i, ∑ j, curl i j (X j * P i)) =
      (fun k => (n + m - 1) • P k - X k * divergence n P) := by
  funext k
  rw [sum_curl_apply, homogeneous_sum_pderiv_X_mul P hP k, sum_pderiv_X_mul]
  have hnm : n + m = (n + m - 1) + 1 := by omega
  rw [hnm, add_nsmul, one_nsmul]
  simp only [Nat.add_sub_cancel]
  simp only [nsmul_eq_mul]
  ring

theorem curl_linearForm_pow (l : Fin n → ℂ) (r : ℕ) (i j : Fin n) :
    curl i j (linearForm l ^ r) =
      (r : ℂ) • shearField l
        (fun k => (Pi.single i (l j) : Fin n → ℂ) k -
          (Pi.single j (l i) : Fin n → ℂ) k) (r - 1) := by
  funext k
  simp only [curl_apply, pderiv_pow, pderiv_linearForm, Pi.smul_apply, shearField,
    Pi.single_apply, smul_eq_C_mul]
  split_ifs <;> simp <;> ring

end Yau.Proofs.Y02Aux
