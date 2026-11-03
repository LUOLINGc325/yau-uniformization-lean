import Yau.Proofs.P06FiberPolynomialCalculus
import Yau.Proofs.G01RawAlgebra

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux.FiberPoly
open Yau
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real polynomial preserves self-adjointness for the original weighted inner product. -/
theorem weighted_power_hermitian (H A : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hA : A.IsHermitian) (hu : IsUnit H.det) (m : ℕ) :
    (H * (H⁻¹ * A) ^ m).IsHermitian := by
  let S := H⁻¹ * A
  have hSH : Sᴴ * H = H * S := by
    dsimp [S]
    rw [Matrix.conjTranspose_mul, hA.eq, hH.inv.eq, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hp : ∀ m : ℕ, (S ^ m)ᴴ * H = H * S ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
      rw [pow_succ, Matrix.conjTranspose_mul, Matrix.mul_assoc, hm,
        ← Matrix.mul_assoc, hSH, Matrix.mul_assoc, ← pow_succ']
      simp only [pow_succ]
  change (H * S ^ m)ᴴ = H * S ^ m
  rw [Matrix.conjTranspose_mul, hH.eq, hp]

theorem weighted_aeval_hermitian (H A : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hA : A.IsHermitian) (hu : IsUnit H.det) (p : Polynomial ℝ) :
    (H * Polynomial.aeval (H⁻¹ * A) p).IsHermitian := by
  classical
  rw [aeval_sum, Matrix.mul_sum]
  change (∑ m ∈ p.support, H * (p.coeff m • (H⁻¹ * A) ^ m))ᴴ = _
  simp only [Matrix.mul_smul, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact ((weighted_power_hermitian H A hH hA hu m).smul (isSelfAdjoint_iff.mpr rfl)).eq

/-- Polynomial evaluation commutes with a change of frame, including noncommuting inputs. -/
theorem aeval_similarity (p : Polynomial ℝ) (S J : Matrix ι ι ℂ)
    (hJ : IsUnit J.det) :
    Polynomial.aeval (J⁻¹ * S * J) p = J⁻¹ * Polynomial.aeval S p * J := by
  have hp : ∀ m : ℕ, (J⁻¹ * S * J) ^ m = J⁻¹ * S ^ m * J := by
    intro m
    induction m with
    | zero => simp only [pow_zero, Matrix.mul_one, Matrix.nonsing_inv_mul _ hJ]
    | succ m hm =>
      rw [pow_succ, hm, pow_succ]
      calc
        _ = J⁻¹ * S ^ m * (J * J⁻¹) * S * J := by noncomm_ring
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hJ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  simp only [aeval_sum, hp, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- The weighted polynomial field transforms by the same congruence as a two-form. -/
theorem weighted_aeval_congruence (p : Polynomial ℝ) (H A J : Matrix ι ι ℂ)
    (hJ : IsUnit J.det) :
    (Jᴴ * H * J) * Polynomial.aeval ((Jᴴ * H * J)⁻¹ * (Jᴴ * A * J)) p =
      Jᴴ * (H * Polynomial.aeval (H⁻¹ * A) p) * J := by
  have hJH : IsUnit Jᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hJ.star
  have he : (Jᴴ * H * J)⁻¹ * (Jᴴ * A * J) = J⁻¹ * (H⁻¹ * A) * J := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc
      _ = J⁻¹ * H⁻¹ * ((Jᴴ)⁻¹ * Jᴴ) * A * J := by noncomm_ring
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hJH]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [he, aeval_similarity p _ _ hJ]
  calc
    _ = Jᴴ * H * (J * J⁻¹) * Polynomial.aeval (H⁻¹ * A) p * J := by noncomm_ring
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hJ]; simp only [Matrix.mul_one, Matrix.mul_assoc]

variable {n : ℕ}

/-- Raw realification is compatible with real polynomial functional calculus. -/
theorem rawReal_aeval (p : Polynomial ℝ) (S : Matrix (Fin n) (Fin n) ℂ) :
    G01Aux.rawReal (Polynomial.aeval S p) = Polynomial.aeval (G01Aux.rawReal S) p := by
  classical
  have hp : ∀ m : ℕ, G01Aux.rawReal (S ^ m) = G01Aux.rawReal S ^ m := by
    intro m
    induction m with
    | zero => exact G01Aux.rawReal_one
    | succ m hm => rw [pow_succ, G01Aux.rawReal_mul, hm, pow_succ]
  simp only [aeval_sum, G01Aux.rawReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← hp]
  ext a b
  simp only [G01Aux.rawReal, Matrix.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  split_ifs <;> ring

end Yau.NodeProofs.P06Aux.FiberPoly
