import Yau.Proofs.V03RectEntries

/-! Actual quadratic forms are bounded by the contract's Euclidean operator
norm, and that norm varies continuously with the finite matrix. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem rectOpNorm_continuous {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (fun A : Matrix ι κ ℂ => rectOpNorm A) := by
  classical
  let Φ : Matrix ι κ ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι) :=
    { toFun := fun A => (Matrix.toEuclideanLin A).toContinuousLinearMap
      map_add' := by
        intro A B
        apply ContinuousLinearMap.ext
        intro v
        change (Matrix.toEuclideanLin (A + B)) v = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c A
        apply ContinuousLinearMap.ext
        intro v
        change (Matrix.toEuclideanLin (c • A)) v = _
        rw [map_smul]
        rfl }
  exact Φ.toContinuousLinearMap.continuous.norm

theorem abs_quadValue_le_rectOpNorm {n : ℕ} (A : CotangentMatrix n)
    (v : CotangentIndex n → ℂ) :
    |quadValue A v| ≤ rectOpNorm A * ∑ i, ‖v i‖ ^ 2 := by
  classical
  let w : EuclideanSpace ℂ (CotangentIndex n) := WithLp.toLp 2 v
  have he : quadValue A v = (inner ℂ w (Matrix.toEuclideanLin A w)).re := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
    rfl
  have hn : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hop : ‖Matrix.toEuclideanLin A w‖ ≤ rectOpNorm A * ‖w‖ :=
    ((Matrix.toEuclideanLin A).toContinuousLinearMap).le_opNorm w
  calc
    _ = |(inner ℂ w (Matrix.toEuclideanLin A w)).re| := congrArg abs he
    _ ≤ ‖inner ℂ w (Matrix.toEuclideanLin A w)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖w‖ * ‖Matrix.toEuclideanLin A w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (rectOpNorm A * ‖w‖) := mul_le_mul_of_nonneg_left hop (norm_nonneg _)
    _ = _ := by rw [← hn]; ring

theorem rectOpNorm_sandwich_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Matrix ι κ ℂ) (H : Matrix ι ι ℂ) :
    rectOpNorm (Eᴴ * H * E) ≤ rectOpNorm E ^ 2 * rectOpNorm H := by
  calc
    _ ≤ rectOpNorm (Eᴴ * H) * rectOpNorm E := V03Proof.rectOpNorm_mul_le _ _
    _ ≤ (rectOpNorm Eᴴ * rectOpNorm H) * rectOpNorm E :=
      mul_le_mul_of_nonneg_right (V03Proof.rectOpNorm_mul_le _ _) (norm_nonneg _)
    _ = _ := by rw [V03Proof.rectOpNorm_conjTranspose]; ring

end Yau.Blueprint.V02Proof
