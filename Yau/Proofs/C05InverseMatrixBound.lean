import Yau.Proofs.C05InverseEnergyNaturalityAlgebra

/-! A coercive form bounds every column of its genuine inverse. This
finite estimate includes the empty index type. -/

noncomputable section
open scoped Matrix

namespace Yau.Proofs.C05Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverseMatrix_column_sq_bound (A : Matrix ι ι ℝ) (hdet : A.det ≠ 0)
    (μ : ℝ) (hμ : 0 < μ)
    (hcoercive : ∀ v : ι → ℝ, μ * (∑ a, v a ^ 2) ≤ v ⬝ᵥ (A *ᵥ v)) (j : ι) :
    μ ^ 2 * (∑ a, (A⁻¹ a j) ^ 2) ≤ 1 := by
  let y : ι → ℝ := A⁻¹ *ᵥ Pi.single j 1
  have hy (a : ι) : y a = A⁻¹ a j := by simp [y]
  have hAy : A *ᵥ y = Pi.single j 1 := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
      (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  let N := ∑ a, y a ^ 2
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hj : y j ^ 2 ≤ N := Finset.single_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset ι)) => sq_nonneg (y a)) (Finset.mem_univ j)
  have hc : μ * N ≤ y j := by
    have hh := hcoercive y
    rw [hAy] at hh
    simpa only [dotProduct_single, mul_one] using hh
  have hyj : 0 ≤ y j := (mul_nonneg hμ.le hN).trans hc
  have hs : (μ * N) ^ 2 ≤ (y j) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hμ.le hN) hyj).2 hc
  have hmul : (μ ^ 2 * N) * N ≤ 1 * N := by nlinarith
  have hb : μ ^ 2 * N ≤ 1 := by
    by_cases hzero : N = 0
    · simp [hzero]
    · exact le_of_mul_le_mul_right hmul (lt_of_le_of_ne hN (Ne.symm hzero))
  simpa only [N, hy] using hb

theorem inverseMatrix_frobenius_sq_bound (A : Matrix ι ι ℝ) (hdet : A.det ≠ 0)
    (μ : ℝ) (hμ : 0 < μ)
    (hcoercive : ∀ v : ι → ℝ, μ * (∑ a, v a ^ 2) ≤ v ⬝ᵥ (A *ᵥ v)) :
    μ ^ 2 * (∑ j, ∑ a, (A⁻¹ a j) ^ 2) ≤ (Fintype.card ι : ℝ) := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum
      (fun j _ => inverseMatrix_column_sq_bound A hdet μ hμ hcoercive j)
    _ = _ := by simp

end Yau.Proofs.C05Aux
