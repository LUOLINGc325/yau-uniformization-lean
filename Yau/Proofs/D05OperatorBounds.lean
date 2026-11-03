import Yau.Proofs.D05MaximumPrinciple
import Yau.Proofs.D05FrobeniusAlgebra
import Yau.Proofs.D05CanonicalAlgebra

/-! Genuine Euclidean matrix operator estimates: Frobenius domination,
transpose invariance, submultiplicativity and the canonical inverse bound. -/

open scoped Topology Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof

theorem matrix_map_norm_sq_le_frob {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (v : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 ≤ matrixFrobSq A * ‖v‖ ^ 2 := by
  have hrow (i : κ) : ‖∑ j, A i j * v j‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 := by
    have habs : ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
      simpa only [norm_mul] using (norm_sum_le Finset.univ (fun j => A i j * v j))
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr habs
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => ‖A i j‖) (fun j => ‖v j‖)
    rw [← EuclideanSpace.norm_sq_eq v] at hcs
    exact hsq.trans hcs
  calc
    ‖Matrix.toEuclideanLin A v‖ ^ 2 = ∑ i, ‖∑ j, A i j * v j‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = matrixFrobSq A * ‖v‖ ^ 2 := by rw [← Finset.sum_mul]; rfl

theorem rectOpNorm_le_of_frobSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) {C : ℝ} (hC : 0 ≤ C) (hA : matrixFrobSq A ≤ C ^ 2) :
    rectOpNorm A ≤ C := by
  classical
  unfold rectOpNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  change ‖Matrix.toEuclideanLin A v‖ ≤ C * ‖v‖
  have hsq := (matrix_map_norm_sq_le_frob A v).trans
    (mul_le_mul_of_nonneg_right hA (sq_nonneg ‖v‖))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  simpa only [mul_pow] using hsq

theorem rectOpNorm_mul_le {ι κ τ : Type*} [Fintype ι]
    [Fintype κ] [Fintype τ]
    (A : Matrix τ κ ℂ) (B : Matrix κ ι ℂ) :
    rectOpNorm (A * B) ≤ rectOpNorm A * rectOpNorm B := by
  classical
  unfold rectOpNorm
  have hmul : (Matrix.toEuclideanLin (A * B)).toContinuousLinearMap =
      (Matrix.toEuclideanLin A).toContinuousLinearMap.comp
        (Matrix.toEuclideanLin B).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 A B) v
  rw [hmul]
  exact ContinuousLinearMap.opNorm_comp_le _ _

def conjugateEuclidean {ι : Type*} (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => star (v i))

theorem conjugateEuclidean_norm {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖conjugateEuclidean v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateEuclidean, norm_star]

theorem rectOpNorm_map_star_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℂ) : rectOpNorm (A.map star) ≤ rectOpNorm A := by
  classical
  unfold rectOpNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have heq : Matrix.toEuclideanLin (A.map star) v =
      conjugateEuclidean (Matrix.toEuclideanLin A (conjugateEuclidean v)) := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, conjugateEuclidean,
      map_sum, star_mul, mul_comm]
  change ‖Matrix.toEuclideanLin (A.map star) v‖ ≤ _
  rw [heq, conjugateEuclidean_norm]
  simpa only [LinearMap.coe_toContinuousLinearMap', conjugateEuclidean_norm] using
    (Matrix.toEuclideanLin A).toContinuousLinearMap.le_opNorm (conjugateEuclidean v)

theorem rectOpNorm_conjTranspose {ι κ : Type*} [Fintype ι]
    [Fintype κ] (A : Matrix κ ι ℂ) :
    rectOpNorm (Matrix.conjTranspose A) = rectOpNorm A := by
  classical
  unfold rectOpNorm
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem rectOpNorm_transpose_le {ι κ : Type*} [Fintype ι]
    [Fintype κ] (A : Matrix κ ι ℂ) :
    rectOpNorm (Matrix.transpose A) ≤ rectOpNorm A := by
  classical
  have heq : (Matrix.conjTranspose A).map star = Matrix.transpose A := by
    ext i j
    simp
  rw [← heq]
  exact (rectOpNorm_map_star_le (Matrix.conjTranspose A)).trans_eq (rectOpNorm_conjTranspose A)

theorem rectOpNorm_negative_canonical_le_one (n : ℕ) :
    rectOpNorm (-(canonicalBivector : CotangentMatrix n)) ≤ 1 := by
  have hJ : Matrix.conjTranspose (-(canonicalBivector : CotangentMatrix n)) *
      -(canonicalBivector : CotangentMatrix n) = 1 := by
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, canonicalBivector_gram]
  unfold rectOpNorm
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖Matrix.toEuclideanLin (-(canonicalBivector : CotangentMatrix n)) v‖ ≤ 1 * ‖v‖
  simpa only [one_mul] using (norm_map_of_column_gram_one _ hJ v).le

end Yau.Blueprint.D05Proof
