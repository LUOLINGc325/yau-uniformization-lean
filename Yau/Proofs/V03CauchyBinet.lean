import Yau.Proofs.V03Coordinates

/-! A rectangular Cauchy--Binet identity indexed by all row tuples. Repeated
rows have zero determinant; summing all tuples avoids choosing ordered minors.
The permutation-cardinality factor also handles the zero-dimensional case. -/

open scoped Matrix ComplexOrder
open Finset Equiv

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem rectangular_det_expand (M : Matrix ι κ ℂ) (N : Matrix κ ι ℂ) :
    (M * N).det = ∑ p : ι → κ,
      (M.submatrix id p).det * ∏ i, N (p i) i := by
  calc
    (M * N).det = ∑ p : ι → κ, ∑ σ : Perm ι,
        (Perm.sign σ : ℂ) * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum,
        Fintype.piFinset_univ]
      rw [sum_comm]
    _ = _ := by
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq, sum_mul,
        prod_mul_distrib, mul_assoc]

theorem rectangular_cauchy_binet_all_tuples (M : Matrix ι κ ℂ) (N : Matrix κ ι ℂ) :
    (Fintype.card (Perm ι) : ℂ) * (M * N).det =
      ∑ p : ι → κ, (M.submatrix id p).det * (N.submatrix p id).det := by
  classical
  symm
  calc
    (∑ p : ι → κ, (M.submatrix id p).det * (N.submatrix p id).det) =
        ∑ σ : Perm ι, ∑ p : ι → κ,
          (M.submatrix id p).det * ((Perm.sign σ : ℂ) * ∏ i, N (p (σ i)) i) := by
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq, mul_sum]
      rw [sum_comm]
    _ = ∑ σ : Perm ι, ∑ p : ι → κ,
        (M.submatrix id (p ∘ σ)).det * ∏ i, N ((p ∘ σ) i) i := by
      apply sum_congr rfl
      intro σ _
      apply sum_congr rfl
      intro p _
      have hp := Matrix.det_permute' σ (M.submatrix id p)
      simp only [Matrix.submatrix_submatrix, Function.comp_id] at hp
      rw [hp]
      simp only [Function.comp_apply]
      ring
    _ = ∑ _σ : Perm ι, (M * N).det := by
      apply sum_congr rfl
      intro σ _
      rw [rectangular_det_expand]
      exact Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl κ))
        (fun p : ι → κ => (M.submatrix id p).det * ∏ i, N (p i) i)
    _ = _ := by simp

theorem gram_det_eq_sum_tuple_minors (J : Matrix κ ι ℂ) :
    (Jᴴ * J).det = (Fintype.card (Perm ι) : ℂ)⁻¹ *
      ∑ p : ι → κ, star ((J.submatrix p id).det) * (J.submatrix p id).det := by
  have h := rectangular_cauchy_binet_all_tuples Jᴴ J
  have hc : (Fintype.card (Perm ι) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Perm ι) ≠ 0)
  have hminor (p : ι → κ) : (Jᴴ.submatrix id p).det = star ((J.submatrix p id).det) := by
    rw [← Matrix.det_conjTranspose]
    rfl
  simp only [hminor] at h
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem star_mul_self_eq_norm_sq (a : ℂ) : star a * a = (‖a‖ ^ 2 : ℝ) := by
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem gram_det_re_eq_sum_tuple_minors (J : Matrix κ ι ℂ) :
    (Jᴴ * J).det.re = (Fintype.card (Perm ι) : ℝ)⁻¹ *
      ∑ p : ι → κ, ‖(J.submatrix p id).det‖ ^ 2 := by
  have h := gram_det_eq_sum_tuple_minors J
  simp only [star_mul_self_eq_norm_sq] at h
  have hc : (Jᴴ * J).det = (((Fintype.card (Perm ι) : ℝ)⁻¹ *
      ∑ p : ι → κ, ‖(J.submatrix p id).det‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum] using h
  exact congrArg Complex.re hc

end Yau.Blueprint.V03Proof
