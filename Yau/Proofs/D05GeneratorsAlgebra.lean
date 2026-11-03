import Yau.Proofs.D05FrameLift
import Yau.Proofs.D05CanonicalAlgebra

/-! The columns of the pushed-forward canonical bivector span precisely
the image of the supplied injective differential, including empty ranks. -/

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof

theorem canonical_generated_right_inverse {n q : ℕ}
    (A : Matrix (Fin q) (CotangentIndex n) ℂ)
    (L : Matrix (CotangentIndex n) (Fin q) ℂ) (hLA : L * A = (1 : CotangentMatrix n)) :
    ((canonicalBivector : CotangentMatrix n) * Matrix.transpose A) *
      (Matrix.transpose L * -(canonicalBivector : CotangentMatrix n)) =
        (1 : CotangentMatrix n) := by
  calc
    _ = (canonicalBivector : CotangentMatrix n) * Matrix.transpose (L * A) * -(canonicalBivector : CotangentMatrix n) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by
      rw [hLA, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_neg,
        canonicalBivector_square, neg_neg]

theorem ambientBivector_mul_right_inverse {n q : ℕ}
    (A : Matrix (Fin q) (CotangentIndex n) ℂ)
    (L : Matrix (CotangentIndex n) (Fin q) ℂ) (hLA : L * A = (1 : CotangentMatrix n)) :
    (A * (canonicalBivector : CotangentMatrix n) * Matrix.transpose A) *
      (Matrix.transpose L * -(canonicalBivector : CotangentMatrix n)) = A := by
  calc
    _ = A * (((canonicalBivector : CotangentMatrix n) * Matrix.transpose A) *
        (Matrix.transpose L * -(canonicalBivector : CotangentMatrix n))) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [canonical_generated_right_inverse A L hLA, Matrix.mul_one]

theorem span_matrix_columns_eq_range {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) :
    Submodule.span ℂ (Set.range fun j : ι =>
      (WithLp.toLp 2 (fun i : κ => A i j) : EuclideanSpace ℂ κ)) =
      LinearMap.range (Matrix.toEuclideanLin A) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨EuclideanSpace.single j 1, ?_⟩
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single,
      Pi.single_apply]
  · rintro _ ⟨v, rfl⟩
    have heq : Matrix.toEuclideanLin A v =
        ∑ j, v j • (WithLp.toLp 2 (fun i : κ => A i j) : EuclideanSpace ℂ κ) := by
      ext i
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

theorem matrix_range_mul_le {ι κ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype τ]
    (A : Matrix τ κ ℂ) (D : Matrix κ ι ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (A * D)) ≤
      LinearMap.range (Matrix.toEuclideanLin A) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨Matrix.toEuclideanLin D v, (LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 A D) v).symm⟩

theorem range_canonical_pushforward {n q : ℕ}
    (A : Matrix (Fin q) (CotangentIndex n) ℂ) (hA : Function.Injective A.mulVec) :
    LinearMap.range (Matrix.toEuclideanLin (A * (canonicalBivector : CotangentMatrix n) * Matrix.transpose A)) =
      LinearMap.range (Matrix.toEuclideanLin A) := by
  obtain ⟨L, hLA⟩ := matrix_leftInverse A hA
  apply le_antisymm
  · rw [Matrix.mul_assoc]
    exact matrix_range_mul_le A ((canonicalBivector : CotangentMatrix n) * Matrix.transpose A)
  · have hle := matrix_range_mul_le
      (A * (canonicalBivector : CotangentMatrix n) * Matrix.transpose A)
      (Matrix.transpose L * -(canonicalBivector : CotangentMatrix n))
    rw [ambientBivector_mul_right_inverse A L hLA] at hle
    exact hle

end Yau.Blueprint.D05Proof
