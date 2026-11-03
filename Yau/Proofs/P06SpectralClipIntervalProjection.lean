import Yau.Proofs.P06SpectralClipInterval

noncomputable section
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
open Yau.NodeProofs.P06Aux

theorem matrix_interval_residual_normal {n : ℕ} (A P U L B : Matrix (Fin n) (Fin n) ℂ)
    (C : ℝ) (hU : U.PosSemidef) (hL : L.PosSemidef)
    (hres : A - P = U - L)
    (hu : U * (C • (1 : Matrix (Fin n) (Fin n) ℂ) - P) = 0)
    (hl : L * (P + C • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0)
    (hbU : (C • (1 : Matrix (Fin n) (Fin n) ℂ) - B).PosSemidef)
    (hbL : (B + C • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    (Matrix.trace ((A - P) * (B - P))).re ≤ 0 := by
  have hup : U * (B - P) = -(U * (C • (1 : Matrix (Fin n) (Fin n) ℂ) - B)) := by
    calc
      _ = U * (C • (1 : Matrix (Fin n) (Fin n) ℂ) - P) -
          U * (C • (1 : Matrix (Fin n) (Fin n) ℂ) - B) := by noncomm_ring
      _ = _ := by rw [hu, zero_sub]
  have hlo : L * (B - P) = L * (B + C • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    calc
      _ = L * (B + C • (1 : Matrix (Fin n) (Fin n) ℂ)) -
          L * (P + C • (1 : Matrix (Fin n) (Fin n) ℂ)) := by noncomm_ring
      _ = _ := by rw [hl, sub_zero]
  have hposU := matrix_trace_mul_nonneg U _ hU hbU
  have hposL := matrix_trace_mul_nonneg L _ hL hbL
  rw [hres, Matrix.sub_mul, hup, hlo, Matrix.trace_sub, Matrix.trace_neg, Complex.sub_re, Complex.neg_re]
  linarith

/-- The actual CFC interval clip has the sharp projection normal inequality
for the same C, including C=0. -/
theorem matrixIntervalClip_normal {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hbU : (C • (1 : Matrix (Fin n) (Fin n) ℂ) - B).PosSemidef)
    (hbL : (B + C • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    (Matrix.trace ((A - matrixIntervalClip C A) * (B - matrixIntervalClip C A))).re ≤ 0 :=
  matrix_interval_residual_normal A _ _ _ B C (matrixIntervalClip_residual_positive C A).1
    (matrixIntervalClip_residual_positive C A).2 (matrixIntervalClip_residual hC A hA)
    (matrixIntervalClip_upper_orthogonal C A hA) (matrixIntervalClip_lower_orthogonal hC A hA) hbU hbL

theorem matrixIntervalClip_nonexpansive {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖matrixToHS (matrixIntervalClip C A - matrixIntervalClip C B)‖ ≤ ‖matrixToHS (A - B)‖ := by
  have hPA := matrixIntervalClip_bounds hC A hA
  have hPB := matrixIntervalClip_bounds hC B hB
  have hnA : inner ℝ (matrixToHS (A - matrixIntervalClip C A))
      (matrixToHS (matrixIntervalClip C B - matrixIntervalClip C A)) ≤ 0 := by
    rw [matrixToHS_inner _ _ (hA.sub (matrixIntervalClip_hermitian C A))]
    exact matrixIntervalClip_normal hC A _ hA hPB.1 hPB.2
  have hnB : inner ℝ (matrixToHS (B - matrixIntervalClip C B))
      (matrixToHS (matrixIntervalClip C A - matrixIntervalClip C B)) ≤ 0 := by
    rw [matrixToHS_inner _ _ (hB.sub (matrixIntervalClip_hermitian C B))]
    exact matrixIntervalClip_normal hC B _ hB hPA.1 hPA.2
  simp only [matrixToHS_sub] at hnA hnB ⊢
  exact norm_sub_le_of_normal_inequalities _ _ _ _ hnA hnB

theorem matrixIntervalClip_distance_sq {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hbU : (C • (1 : Matrix (Fin n) (Fin n) ℂ) - B).PosSemidef)
    (hbL : (B + C • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    ‖matrixToHS (matrixIntervalClip C A - B)‖ ^ 2 ≤ ‖matrixToHS (A - B)‖ ^ 2 -
      ‖matrixToHS (A - matrixIntervalClip C A)‖ ^ 2 := by
  have hn : inner ℝ (matrixToHS (A - matrixIntervalClip C A))
      (matrixToHS (B - matrixIntervalClip C A)) ≤ 0 := by
    rw [matrixToHS_inner _ _ (hA.sub (matrixIntervalClip_hermitian C A))]
    exact matrixIntervalClip_normal hC A B hA hbU hbL
  simp only [matrixToHS_sub] at hn ⊢
  exact distance_sq_le_of_normal_inequality _ _ _ hn

theorem matrixIntervalClip_eq_self {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hU : (C • (1 : Matrix (Fin n) (Fin n) ℂ) - A).PosSemidef)
    (hL : (A + C • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) : matrixIntervalClip C A = A := by
  have hn := matrixIntervalClip_normal hC A A hA hU hL
  rw [← matrixToHS_inner _ _ (hA.sub (matrixIntervalClip_hermitian C A)),
    real_inner_self_eq_norm_sq] at hn
  have hz : matrixToHS (A - matrixIntervalClip C A) = 0 :=
    norm_eq_zero.mp (by nlinarith [norm_nonneg (matrixToHS (A - matrixIntervalClip C A))])
  have he : A - matrixIntervalClip C A = 0 :=
    matrixToHS_injective n (hz.trans (show matrixToHS (0 : Matrix (Fin n) (Fin n) ℂ) = 0 from rfl).symm)
  exact (sub_eq_zero.mp he).symm

theorem matrixIntervalClip_zero {n : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    matrixIntervalClip C (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  rw [matrixIntervalClip, cfc_apply_zero, intervalClip_zero hC, map_zero]

theorem matrixIntervalClip_zero_width {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixIntervalClip 0 A = 0 := by
  have hf : intervalClip 0 = (0 : ℝ → ℝ) := by
    funext r
    simpa only [intervalClip, neg_zero, Pi.zero_apply] using min_eq_left (le_max_left 0 r)
  rw [matrixIntervalClip, hf, cfc_zero]

end Yau.NodeProofs.P06Aux.Clip
