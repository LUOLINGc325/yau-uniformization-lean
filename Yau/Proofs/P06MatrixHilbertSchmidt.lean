import Yau.Proofs.P06SpectralClipPositivePart

noncomputable section
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip

/-- The genuine Euclidean Hilbert space of matrix entries. This gives the
Hilbert–Schmidt norm without changing any norm instance on matrices. -/
def matrixToHS {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

theorem matrixToHS_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixToHS (A - B) = matrixToHS A - matrixToHS B := rfl

theorem matrixToHS_injective (n : ℕ) : Function.Injective (matrixToHS (n := n)) := by
  intro A B he
  ext i j
  exact congrArg (fun v : EuclideanSpace ℂ (Fin n × Fin n) => v (i, j)) he

theorem matrixToHS_inner {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    inner ℝ (matrixToHS A) (matrixToHS B) = (Matrix.trace (A * B)).re := by
  have hs (i j : Fin n) : star (A i j) = A j i := by
    simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA j) i
  rw [PiLp.inner_apply]
  simp only [matrixToHS, PiLp.toLp_apply, real_inner_eq_re_inner ℂ, RCLike.re_eq_complex_re]
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  simp only [RCLike.inner_apply', Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [← Complex.star_def, hs]
  exact Finset.sum_comm

theorem norm_sub_le_of_normal_inequalities {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y px py : H) (hx : inner ℝ (x - px) (py - px) ≤ 0)
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

theorem distance_sq_le_of_normal_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x p b : H) (hnormal : inner ℝ (x - p) (b - p) ≤ 0) :
    ‖p - b‖ ^ 2 ≤ ‖x - b‖ ^ 2 - ‖x - p‖ ^ 2 := by
  have he : (x - p) - (b - p) = x - b := by abel
  have hn := norm_sub_sq_real (x - p) (b - p)
  rw [he, norm_sub_rev b p] at hn
  linarith

/-- Positive-part projection is nonexpansive in the actual entry Hilbert
norm, including arbitrary signed Hermitian matrices. -/
theorem matrixPositivePart_nonexpansive {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖matrixToHS (matrixPositivePart A - matrixPositivePart B)‖ ≤ ‖matrixToHS (A - B)‖ := by
  have hPA := matrixPositivePart_posSemidef A
  have hPB := matrixPositivePart_posSemidef B
  have hAn : inner ℝ (matrixToHS (A - matrixPositivePart A))
      (matrixToHS (matrixPositivePart B - matrixPositivePart A)) ≤ 0 := by
    rw [matrixToHS_inner _ _ (hA.sub hPA.1)]
    exact matrixPositivePart_normal A _ hA hPB
  have hBn : inner ℝ (matrixToHS (B - matrixPositivePart B))
      (matrixToHS (matrixPositivePart A - matrixPositivePart B)) ≤ 0 := by
    rw [matrixToHS_inner _ _ (hB.sub hPB.1)]
    exact matrixPositivePart_normal B _ hB hPA
  simp only [matrixToHS_sub] at hAn hBn ⊢
  exact norm_sub_le_of_normal_inequalities _ _ _ _ hAn hBn

theorem matrixPositivePart_distance_sq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    ‖matrixToHS (matrixPositivePart A - B)‖ ^ 2 ≤ ‖matrixToHS (A - B)‖ ^ 2 -
      ‖matrixToHS (A - matrixPositivePart A)‖ ^ 2 := by
  have hn : inner ℝ (matrixToHS (A - matrixPositivePart A))
      (matrixToHS (B - matrixPositivePart A)) ≤ 0 := by
    rw [matrixToHS_inner _ _ (hA.sub (matrixPositivePart_posSemidef A).1)]
    exact matrixPositivePart_normal A B hA hB
  simp only [matrixToHS_sub] at hn ⊢
  exact distance_sq_le_of_normal_inequality _ _ _ hn

theorem matrixPositivePart_eq_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) : matrixPositivePart A = A :=
  (CFC.posPart_eq_self A).mpr hA.nonneg

theorem matrixPositivePart_zero (n : ℕ) : matrixPositivePart (0 : Matrix (Fin n) (Fin n) ℂ) = 0 :=
  CFC.posPart_zero

end Yau.NodeProofs.P06Aux.Clip
