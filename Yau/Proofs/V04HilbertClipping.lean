import Yau.Proofs.V04HermitianCalculus

/-! Frobenius contraction for the actual frozen negative part. The proof
uses the positive-cone projection in the Euclidean space of all entries;
no operator-norm Lipschitz assertion is used. -/

open scoped InnerProductSpace ComplexOrder MatrixOrder

noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

def cotangentMatrixHS (A : CotangentMatrix n) :
    EuclideanSpace ℂ (CotangentIndex n × CotangentIndex n) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

theorem cotangentMatrixHS_sub (A B : CotangentMatrix n) :
    cotangentMatrixHS (A - B) = cotangentMatrixHS A - cotangentMatrixHS B := rfl

theorem cotangentMatrixHS_norm_sq (A : CotangentMatrix n) :
    ‖cotangentMatrixHS A‖ ^ 2 = matrixFrobSq A := by
  simp only [EuclideanSpace.norm_sq_eq, cotangentMatrixHS, PiLp.toLp_apply,
    Fintype.sum_prod_type, matrixFrobSq]

theorem cotangentMatrixHS_inner (A B : CotangentMatrix n) (hA : A.IsHermitian) :
    inner ℝ (cotangentMatrixHS A) (cotangentMatrixHS B) = (Matrix.trace (A * B)).re := by
  have hs (i j : CotangentIndex n) : star (A i j) = A j i := by
    simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA j) i
  rw [PiLp.inner_apply]
  simp only [cotangentMatrixHS, PiLp.toLp_apply, real_inner_eq_re_inner ℂ,
    RCLike.re_eq_complex_re]
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  simp only [RCLike.inner_apply', Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [← Complex.star_def, hs]
  exact Finset.sum_comm

private theorem trace_mul_nonneg (A B : CotangentMatrix n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re := by
  let C := CFC.sqrt B
  have hC : C.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).1
  have hsq : C * C = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hpos := hA.mul_mul_conjTranspose_same C
  rw [hC.eq] at hpos
  have htr := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  have heq : Matrix.trace (C * A * C) = Matrix.trace (A * B) := by
    rw [Matrix.trace_mul_cycle, hsq, Matrix.trace_mul_comm]
  rwa [heq] at htr

theorem matrixPositive_normal (A B : CotangentMatrix n)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    (Matrix.trace ((A - matrixPositive A) * (B - matrixPositive A))).re ≤ 0 := by
  have htr := trace_mul_nonneg (matrixNegative A) B (matrixNegative_posSemidef A) hB
  have hd : A - matrixPositive A = -matrixNegative A := by
    have he := matrixPositive_sub_matrixNegative A hA
    calc
      A - matrixPositive A =
          (matrixPositive A - matrixNegative A) - matrixPositive A :=
        congrArg (fun D => D - matrixPositive A) he.symm
      _ = -matrixNegative A := by abel
  rw [hd, neg_mul, Matrix.mul_sub, matrixNegative_mul_matrixPositive A hA,
    sub_zero, Matrix.trace_neg, Complex.neg_re]
  exact neg_nonpos.mpr htr

private theorem projection_norm_sub_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x y px py : H)
    (hx : inner ℝ (x - px) (py - px) ≤ 0)
    (hy : inner ℝ (y - py) (px - py) ≤ 0) : ‖px - py‖ ≤ ‖x - y‖ := by
  let d := px - py
  have hx' : 0 ≤ inner ℝ (x - px) d := by
    have he : py - px = -d := by dsimp only [d]; abel
    rw [he, inner_neg_right] at hx
    exact neg_nonpos.mp hx
  have hh : 0 ≤ inner ℝ ((x - px) - (y - py)) d := by
    rw [inner_sub_left]
    exact sub_nonneg.mpr (hy.trans hx')
  have he : (x - px) - (y - py) = (x - y) - d := by dsimp only [d]; abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq] at hh
  have hcs := real_inner_le_norm (x - y) d
  by_cases hd : d = 0
  · simpa only [show px - py = d from rfl, hd, norm_zero] using norm_nonneg (x - y)
  · have hp : 0 < ‖d‖ := norm_pos_iff.mpr hd
    apply (mul_le_mul_iff_left₀ hp).mp
    change ‖d‖ * ‖d‖ ≤ ‖x - y‖ * ‖d‖
    nlinarith

theorem matrixPositive_HS_nonexpansive (A B : CotangentMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖cotangentMatrixHS (matrixPositive A - matrixPositive B)‖ ≤
      ‖cotangentMatrixHS (A - B)‖ := by
  have hPA := matrixPositive_posSemidef A
  have hPB := matrixPositive_posSemidef B
  have hnA : inner ℝ (cotangentMatrixHS (A - matrixPositive A))
      (cotangentMatrixHS (matrixPositive B - matrixPositive A)) ≤ 0 := by
    rw [cotangentMatrixHS_inner _ _ (hA.sub hPA.1)]
    exact matrixPositive_normal A _ hA hPB
  have hnB : inner ℝ (cotangentMatrixHS (B - matrixPositive B))
      (cotangentMatrixHS (matrixPositive A - matrixPositive B)) ≤ 0 := by
    rw [cotangentMatrixHS_inner _ _ (hB.sub hPB.1)]
    exact matrixPositive_normal B _ hB hPA
  simp only [cotangentMatrixHS_sub] at hnA hnB ⊢
  exact projection_norm_sub_le _ _ _ _ hnA hnB

theorem matrixNegative_HS_nonexpansive (A B : CotangentMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖cotangentMatrixHS (matrixNegative A - matrixNegative B)‖ ≤
      ‖cotangentMatrixHS (A - B)‖ := by
  have hNA : matrixPositive (-A) = matrixNegative A := by
    rw [matrixPositive_eq_posPart (-A) hA.neg, matrixNegative_eq_negPart A hA,
      CFC.posPart_neg]
  have hNB : matrixPositive (-B) = matrixNegative B := by
    rw [matrixPositive_eq_posPart (-B) hB.neg, matrixNegative_eq_negPart B hB,
      CFC.posPart_neg]
  have h := matrixPositive_HS_nonexpansive (-A) (-B) hA.neg hB.neg
  rw [hNA, hNB] at h
  have hid : -A - -B = -(A - B) := by abel
  simpa only [hid, show cotangentMatrixHS (-(A - B)) = -cotangentMatrixHS (A - B) from rfl,
    norm_neg] using h

theorem matrixNegative_frobSq_sub_le (A B : CotangentMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matrixFrobSq (matrixNegative A - matrixNegative B) ≤ matrixFrobSq (A - B) := by
  rw [← cotangentMatrixHS_norm_sq, ← cotangentMatrixHS_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (matrixNegative_HS_nonexpansive A B hA hB)

end Yau.Blueprint.V04Proof
