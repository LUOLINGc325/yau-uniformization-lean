import Yau.Proofs.V03VelocityBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Native Euclidean operator norm calculus for the exact rectangular
operator norm in the contract, including zero-dimensional index spaces. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem rectOpNorm_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    0 ≤ rectOpNorm A := norm_nonneg _

theorem rectOpNorm_mul_le {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (A : Matrix ι κ ℂ) (B : Matrix κ τ ℂ) :
    rectOpNorm (A * B) ≤ rectOpNorm A * rectOpNorm B := by
  classical
  unfold rectOpNorm
  change ‖(Matrix.toLpLin 2 2 (A * B)).toContinuousLinearMap‖ ≤ _
  rw [Matrix.toLpLin_mul 2 2 2]
  have hc : ((Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 B)).toContinuousLinearMap =
      ((Matrix.toLpLin 2 2 A).toContinuousLinearMap).comp
        ((Matrix.toLpLin 2 2 B).toContinuousLinearMap) := by ext v; rfl
  rw [hc]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem rectOpNorm_conjTranspose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : rectOpNorm Aᴴ = rectOpNorm A := by
  classical
  unfold rectOpNorm
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  exact LinearIsometryEquiv.norm_map _ _

theorem rectOpNorm_le_one_of_gram {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) : rectOpNorm U ≤ 1 := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖(WithLp.toLp 2 (U *ᵥ WithLp.ofLp v) : EuclideanSpace ℂ ι)‖ ≤ 1 * ‖v‖
  rw [euclidean_mulVec_norm_of_gram_eq_one U hU]
  simp only [WithLp.toLp_ofLp, one_mul, le_refl]

theorem rectOpNorm_frame_contraction_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) (B : Matrix ι ι ℂ) :
    rectOpNorm (Uᴴ * B * U) ≤ rectOpNorm B := by
  have hu := rectOpNorm_le_one_of_gram U hU
  have hhu : rectOpNorm Uᴴ ≤ 1 := by rwa [rectOpNorm_conjTranspose]
  calc
    _ ≤ (rectOpNorm Uᴴ * rectOpNorm B) * rectOpNorm U :=
      (rectOpNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (rectOpNorm_mul_le _ _) (rectOpNorm_nonneg U))
    _ ≤ (1 * rectOpNorm B) * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hhu (rectOpNorm_nonneg B)) hu
        (rectOpNorm_nonneg U) (mul_nonneg zero_le_one (rectOpNorm_nonneg B))
    _ = _ := by ring

end Yau.Blueprint.V03Proof
