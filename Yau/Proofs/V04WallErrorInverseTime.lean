import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Differentiation of the genuine inverse matrix on a relative time set.
The argument applies at the initial endpoint without a time extension. -/

open Filter
open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_differentiableWithinAt
    {A : ℝ → Matrix ι ι ℂ} {S : Set ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun s => A s i j) S t) :
    DifferentiableWithinAt ℝ (fun s => (A s).det) S t := by
  simp_rw [Matrix.det_apply']
  have hd (σ : Equiv.Perm ι) : DifferentiableWithinAt ℝ
      (fun s => (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, A s (σ i) i) S t :=
    (differentiableWithinAt_const _).mul
      (DifferentiableWithinAt.fun_finsetProd fun i _ => hA (σ i) i)
  exact DifferentiableWithinAt.fun_sum (u := Finset.univ) (fun σ _ => hd σ)

theorem matrix_inverse_differentiableWithinAt
    {A : ℝ → Matrix ι ι ℂ} {S : Set ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableWithinAt ℝ (fun s => A s i j) S t)
    (hdet : (A t).det ≠ 0) (i j : ι) :
    DifferentiableWithinAt ℝ (fun s => (A s)⁻¹ i j) S t := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply]
  apply ((matrix_det_differentiableWithinAt hA).inv hdet).mul
  apply matrix_det_differentiableWithinAt
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact differentiableWithinAt_const _
  · simp only [hkj, ↓reduceIte]
    exact hA k l

/-- An inverse derivative obtained by differentiating `A A⁻¹ = 1` within
its actual time set. All inverse values used in the identity are invertible. -/
theorem matrix_inverse_hasDerivWithinAt
    {A : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {S : Set ℝ} {t : ℝ}
    (ht : t ∈ S) (hS : UniqueDiffWithinAt ℝ S t)
    (hA : ∀ i j, HasDerivWithinAt (fun s => A s i j) (D i j) S t)
    (hi : ∀ i j, DifferentiableWithinAt ℝ (fun s => (A s)⁻¹ i j) S t)
    (hdet : ∀ s ∈ S, IsUnit (A s).det) (i j : ι) :
    HasDerivWithinAt (fun s => (A s)⁻¹ i j)
      ((-(A t)⁻¹ * D * (A t)⁻¹) i j) S t := by
  let E : Matrix ι ι ℂ := fun i j => derivWithin (fun s => (A s)⁻¹ i j) S t
  have hE (i j : ι) : HasDerivWithinAt (fun s => (A s)⁻¹ i j) (E i j) S t :=
    (hi i j).hasDerivWithinAt
  have hzero : D * (A t)⁻¹ + A t * E = 0 := by
    ext i j
    have hp := HasDerivWithinAt.fun_sum (u := Finset.univ)
      (fun k _ => (hA i k).mul (hE k j))
    have heq : (fun s => ∑ k, A s i k * (A s)⁻¹ k j) =ᶠ[𝓝[S] t]
        (fun _ => (1 : Matrix ι ι ℂ) i j) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact congrArg (fun B : Matrix ι ι ℂ => B i j)
        (Matrix.mul_nonsing_inv (A s) (hdet s hs))
    have hp' := hp.congr_of_eventuallyEq heq.symm
      (congrArg (fun B : Matrix ι ι ℂ => B i j) (Matrix.mul_nonsing_inv (A t) (hdet t ht))).symm
    have hz := hp'.derivWithin hS
    have hconst := (hasDerivWithinAt_const t S ((1 : Matrix ι ι ℂ) i j)).derivWithin hS
    rw [hconst] at hz
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      Finset.sum_add_distrib, derivWithin_const, Pi.zero_apply] using hz.symm
  have hsolve : E = -(A t)⁻¹ * D * (A t)⁻¹ := by
    have he := congrArg (fun B => (A t)⁻¹ * B) hzero
    rw [Matrix.mul_add, ← Matrix.mul_assoc ((A t)⁻¹) (A t) E,
      Matrix.nonsing_inv_mul _ (hdet t ht), Matrix.one_mul, Matrix.mul_zero] at he
    exact (eq_neg_of_add_eq_zero_right he).trans (by simp only [Matrix.neg_mul, Matrix.mul_assoc])
  rw [← hsolve]
  exact hE i j

/-- The relative inverse derivative needs only derivatives of the original
matrix and genuine invertibility on the relative domain. -/
theorem matrix_inverse_hasDerivWithinAt_of_entries
    {A : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} {S : Set ℝ} {t : ℝ}
    (ht : t ∈ S) (hS : UniqueDiffWithinAt ℝ S t)
    (hA : ∀ i j, HasDerivWithinAt (fun s => A s i j) (D i j) S t)
    (hdet : ∀ s ∈ S, IsUnit (A s).det) (i j : ι) :
    HasDerivWithinAt (fun s => (A s)⁻¹ i j)
      ((-(A t)⁻¹ * D * (A t)⁻¹) i j) S t :=
  matrix_inverse_hasDerivWithinAt ht hS hA
    (matrix_inverse_differentiableWithinAt (fun i j => (hA i j).differentiableWithinAt)
      ((hdet t ht).ne_zero)) hdet i j

end Yau.Blueprint.V04Proof.WallErrorAux
