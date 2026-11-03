import Yau.Proofs.P06WeakLeviPositiveTests

noncomputable section
open scoped ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint

def polarizationVectors {n : ℕ} (u v : Fin n → ℂ) : Fin 4 → (Fin n → ℂ) :=
  ![u + v, u - v, u + Complex.I • v, u - Complex.I • v]

def polarizationCoefficients (c : ℂ) : Fin 4 → ℝ :=
  ![c.re / 4, -c.re / 4, -c.im / 4, c.im / 4]

theorem polarization_rankOne {n : ℕ} (c : ℂ) (u v : Fin n → ℂ) :
    (∑ r : Fin 4, (polarizationCoefficients c r : ℂ) •
      Matrix.vecMulVec (polarizationVectors u v r) (star (polarizationVectors u v r))) =
      (c / 2) • Matrix.vecMulVec u (star v) +
        (star c / 2) • Matrix.vecMulVec v (star u) := by
  ext a b
  simp only [Fin.sum_univ_four, polarizationCoefficients, polarizationVectors,
    Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.div_ofNat] <;> ring

theorem matrix_sum_rankOne_units {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, A i j • Matrix.vecMulVec (Pi.single i 1) (star (Pi.single j 1))) = A := by
  classical
  ext a b
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.single_apply, smul_eq_mul, mul_ite]

def hermitianTestVectors (n : ℕ) : ((Fin n × Fin n) × Fin 4) → ComplexVector n :=
  fun p => WithLp.toLp 2 (polarizationVectors (Pi.single p.1.1 1) (Pi.single p.1.2 1) p.2)

def hermitianTestCoefficients {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((Fin n × Fin n) × Fin 4) → ℝ := fun p => polarizationCoefficients (A p.1.1 p.1.2) p.2

/-- Every Hermitian test uses one fixed finite family of constant
directions, with coefficients linear in its actual entries. No smooth
choice of eigenvectors or square roots is used. -/
theorem hermitianTestDecomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    (∑ p, (hermitianTestCoefficients A p : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp (hermitianTestVectors n p))
        (star (WithLp.ofLp (hermitianTestVectors n p)))) = A := by
  classical
  simp only [hermitianTestCoefficients, hermitianTestVectors, WithLp.ofLp_toLp,
    Fintype.sum_prod_type]
  simp_rw [polarization_rankOne]
  simp only [Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin n, ∑ j : Fin n, (A i j / 2) •
      Matrix.vecMulVec (Pi.single i 1) (star (Pi.single j 1))) = (1 / 2 : ℂ) • A := by
    calc
      _ = (1 / 2 : ℂ) • (∑ i, ∑ j, A i j •
          Matrix.vecMulVec (Pi.single i 1) (star (Pi.single j 1))) := by
        simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv, one_mul, mul_comm]
      _ = _ := congrArg ((1 / 2 : ℂ) • ·) (matrix_sum_rankOne_units A)
  rw [hfirst]
  have hstar (i j : Fin n) : star (A i j) = A j i := by
    simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA j) i
  simp_rw [hstar]
  rw [Finset.sum_comm, hfirst]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Yau.NodeProofs.P06Aux
