import Yau.Proofs.P06OrderAlgebra

noncomputable section

namespace Yau.NodeProofs.P06Aux.Clip

/-- The full noncommutative differential of a power, with the variation
inserted in every position. Its recursion is the actual Leibniz rule. -/
def powerVariation {A : Type*} [Semiring A] (S D : A) : ℕ → A
  | 0 => 0
  | m + 1 => powerVariation S D m * S + S ^ m * D

theorem powerVariation_zero {A : Type*} [Semiring A] (S : A) (m : ℕ) :
    powerVariation S 0 m = 0 := by
  induction m with
  | zero => rfl
  | succ m hm => simp only [powerVariation, hm, zero_mul, mul_zero, add_zero]

theorem powerVariation_add {A : Type*} [Semiring A] (S D E : A) (m : ℕ) :
    powerVariation S (D + E) m = powerVariation S D m + powerVariation S E m := by
  induction m with
  | zero => simp only [powerVariation, add_zero]
  | succ m hm => simp only [powerVariation, hm, add_mul, mul_add]; abel

theorem powerVariation_map {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (S D : A) (m : ℕ) :
    powerVariation (f S) (f D) m = f (powerVariation S D m) := by
  induction m with
  | zero => exact f.map_zero.symm
  | succ m hm => simp only [powerVariation, hm, map_add, map_mul, map_pow]

theorem powerVariation_commutator {A : Type*} [Ring A] (S Γ : A) (m : ℕ) :
    powerVariation S (Γ * S - S * Γ) m = Γ * S ^ m - S ^ m * Γ := by
  induction m with
  | zero => simp only [powerVariation, pow_zero, mul_one, one_mul, sub_self]
  | succ m hm => rw [powerVariation, hm, pow_succ]; noncomm_ring

def powerSlope {R : Type*} [Semiring R] (a b : R) : ℕ → R
  | 0 => 0
  | m + 1 => powerSlope a b m * b + a ^ m

/-- The divided difference identity holds before division; coincident
eigenvalues are therefore included in the same finite calculation. -/
theorem powerSlope_mul_sub {R : Type*} [CommRing R] (a b : R) (m : ℕ) :
    powerSlope a b m * (a - b) = a ^ m - b ^ m := by
  induction m with
  | zero => simp only [powerSlope, zero_mul, pow_zero, sub_self]
  | succ m hm =>
      rw [powerSlope, pow_succ, pow_succ]
      calc
        _ = (powerSlope a b m * (a - b)) * b + a ^ m * (a - b) := by ring
        _ = _ := by rw [hm]; ring

theorem powerSlope_self {R : Type*} [CommRing R] (a : R) (m : ℕ) :
    powerSlope a a m = (m : R) * a ^ (m - 1) := by
  induction m with
  | zero => simp only [powerSlope, Nat.cast_zero, zero_mul]
  | succ m hm =>
      by_cases hm0 : m = 0
      · subst m; simp only [powerSlope, pow_zero, zero_mul, zero_add, Nat.cast_one,
          Nat.reduceSub, one_mul]
      · have hp : a ^ (m - 1) * a = a ^ m := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
        rw [powerSlope, hm]
        simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
        calc
          _ = (m : R) * (a ^ (m - 1) * a) + a ^ m := by ring
          _ = _ := by rw [hp]; ring

theorem powerVariation_diagonal_apply {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (lam : ι → R) (D : Matrix ι ι R) (m : ℕ) (i j : ι) :
    powerVariation (Matrix.diagonal lam) D m i j = D i j * powerSlope (lam i) (lam j) m := by
  induction m with
  | zero => simp only [powerVariation, Matrix.zero_apply, powerSlope, mul_zero]
  | succ m hm =>
      simp only [powerVariation, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_pow,
        Matrix.diagonal_mul, Pi.pow_apply, hm, powerSlope]
      ring

end Yau.NodeProofs.P06Aux.Clip
