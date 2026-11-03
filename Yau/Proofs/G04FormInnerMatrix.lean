import Yau.Proofs.G04SignedFormInverse
import Yau.Proofs.G01Realification
import Yau.LeafProofs.L23RicciBound

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def realFormMatrix (A : RealForm M 2) (x : M.Carrier) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun a b => A x ![chartVec x x (realVec a), chartVec x x (realVec b)]

theorem realFormMatrix_skew (A : RealForm M 2) (x : M.Carrier) (a b : RIdx n) :
    realFormMatrix A x b a = -realFormMatrix A x a b := by
  simpa only [centeredForm_apply, realFormMatrix] using
    alternating_two_swap (centeredForm A x) (realVec a) (realVec b)

theorem formComponents_center_pair (A : RealForm M 2) (x : M.Carrier) (I : Fin 2 → RIdx n) :
    formComponents A x (chartPt x x) I = realFormMatrix A x (I 0) (I 1) := by
  rw [L03.formComponents_apply_of_mem_source A x x (mem_extChartAt_source x)]
  simp only [L03.localRealBasis_apply]
  unfold realFormMatrix
  congr 1
  ext r
  fin_cases r <;> rfl

theorem formInner_two (h : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) :
    formInner h A B x = (1 / 2 : ℝ) * ∑ a, ∑ b, ∑ c, ∑ d,
      realFormMatrix A x a b * realFormMatrix B x c d *
        (realMetricFn h x (chartPt x x))⁻¹ a c * (realMetricFn h x (chartPt x x))⁻¹ b d := by
  unfold formInner
  simp only [formComponents_center_pair, L23Aux.sum_tensor_cons,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_one, Fin.cons_succ,
    Fintype.sum_unique, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, mul_one]
  congr 1
  · norm_num
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_four_rotate (F : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = ∑ b, ∑ d, ∑ c, F a b c d := by
          apply Finset.sum_congr rfl
          intro b _
          exact Finset.sum_comm
        _ = ∑ d, ∑ b, ∑ c, F a b c d := Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem trace_four (G K H L : Matrix ι ι ℝ) :
    Matrix.trace (G * K * H * L) = ∑ a, ∑ b, ∑ c, ∑ d,
      G a b * K b c * H c d * L d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ d, ∑ c, ∑ b, (G a b * K b c) * H c d * L d a) =
        ∑ d, ∑ b, ∑ c, (G a b * K b c) * H c d * L d a := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, (G a b * K b c) * H c d * L d a := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

theorem alternating_contraction_trace (G K L : Matrix ι ι ℝ) (hG : G.IsSymm)
    (hL : ∀ a b, L b a = -L a b) :
    (∑ a, ∑ b, ∑ c, ∑ d, K a b * L c d * G a c * G b d) =
      -Matrix.trace (G * K * G * L) := by
  have he : Matrix.trace (G * K * G * L) =
      -(∑ a, ∑ b, ∑ c, ∑ d, K a b * L c d * G a c * G b d) := by
    rw [trace_four]
    rw [← sum_four_rotate (fun a b c d => G d a * K a b * G b c * L c d)]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [hG.apply a c, hL c d]
    ring
  linarith

end Finite

theorem formInner_trace (h : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) :
    formInner h A B x = -(1 / 2 : ℝ) * Matrix.trace
      ((realMetricFn h x (chartPt x x))⁻¹ * realFormMatrix A x *
        (realMetricFn h x (chartPt x x))⁻¹ * realFormMatrix B x) := by
  rw [formInner_two, alternating_contraction_trace _ _ _
    (L12Aux.realMetricFn_isSymm h x (chartPt x x)).inv (realFormMatrix_skew B x)]
  ring

theorem matrixImagBilin_basis_raw (A : Matrix (Fin n) (Fin n) ℂ) (a b : RIdx n) :
    matrixImagBilin A (realVec a) (realVec b) =
      ((-2 : ℝ) • (G01Aux.rawReal A * L12Aux.jMatrix n)) a b := by
  rw [Matrix.smul_apply, L12Aux.mul_jMatrix, matrixImagBilin_apply]
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [matrixPairing, G01Aux.rawReal, L12Aux.jIndex, L12Aux.jSign,
      realVec, EuclideanSpace.single, apply_ite, Complex.mul_re, Complex.mul_im]

theorem realFormMatrix_eq_raw (A : RealForm M 2) (hA : RealOneOne A) (x : M.Carrier) :
    realFormMatrix A x = (-2 : ℝ) • (G01Aux.rawReal (formHermitianMatrix A x) * L12Aux.jMatrix n) := by
  ext a b
  have he := (representsSelf A hA).1 x (realVec a) (realVec b)
  change realFormMatrix A x a b = matrixImagBilin (formHermitianMatrix A x) (realVec a) (realVec b) at he
  exact he.trans (matrixImagBilin_basis_raw _ a b)

theorem rawReal_commute_J (A : Matrix (Fin n) (Fin n) ℂ) :
    L12Aux.jMatrix n * G01Aux.rawReal A = G01Aux.rawReal A * L12Aux.jMatrix n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [L12Aux.jMatrix_mul, L12Aux.mul_jMatrix]
  fin_cases a <;> fin_cases b <;>
    simp [G01Aux.rawReal, L12Aux.jIndex, L12Aux.jSign]

theorem formInner_oneOne (h : HermitianField M) (A B : RealForm M 2)
    (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier) :
    formInner h A B x = (Matrix.trace ((gMat h x)⁻¹ * formHermitianMatrix A x *
      (gMat h x)⁻¹ * formHermitianMatrix B x)).re := by
  let H := gMat h x
  let C := formHermitianMatrix A x
  let D := formHermitianMatrix B x
  have hinv : (realMetricFn h x (chartPt x x))⁻¹ =
      (1 / 2 : ℝ) • G01Aux.rawReal H⁻¹ :=
    G01Aux.realMetricFn_inverse_eq h x (chartPt x x) (mem_extChartAt_target x)
  rw [formInner_trace, hinv, realFormMatrix_eq_raw A hA x, realFormMatrix_eq_raw B hB x]
  change -(1 / 2 : ℝ) * Matrix.trace
    (((1 / 2 : ℝ) • G01Aux.rawReal H⁻¹) * ((-2 : ℝ) • (G01Aux.rawReal C * L12Aux.jMatrix n)) *
      ((1 / 2 : ℝ) • G01Aux.rawReal H⁻¹) * ((-2 : ℝ) • (G01Aux.rawReal D * L12Aux.jMatrix n))) = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) * (1 / 2) * (-2) = 1 by norm_num, one_smul]
  have hp : G01Aux.rawReal H⁻¹ * (G01Aux.rawReal C * L12Aux.jMatrix n) *
      G01Aux.rawReal H⁻¹ * (G01Aux.rawReal D * L12Aux.jMatrix n) =
      -G01Aux.rawReal (H⁻¹ * C * H⁻¹ * D) := by
    calc
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C *
          (L12Aux.jMatrix n * G01Aux.rawReal H⁻¹) * G01Aux.rawReal D * L12Aux.jMatrix n := by noncomm_ring
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C *
          (G01Aux.rawReal H⁻¹ * L12Aux.jMatrix n) * G01Aux.rawReal D * L12Aux.jMatrix n := by rw [rawReal_commute_J]
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C * G01Aux.rawReal H⁻¹ *
          (L12Aux.jMatrix n * G01Aux.rawReal D) * L12Aux.jMatrix n := by noncomm_ring
      _ = G01Aux.rawReal H⁻¹ * G01Aux.rawReal C * G01Aux.rawReal H⁻¹ *
          (G01Aux.rawReal D * L12Aux.jMatrix n) * L12Aux.jMatrix n := by rw [rawReal_commute_J]
      _ = -(G01Aux.rawReal H⁻¹ * G01Aux.rawReal C * G01Aux.rawReal H⁻¹ * G01Aux.rawReal D) := by
        simp only [Matrix.mul_assoc, L12Aux.jMatrix_sq, Matrix.mul_neg, Matrix.mul_one]
      _ = _ := by simp only [G01Aux.rawReal_mul]
  rw [hp, Matrix.trace_neg, G01Aux.rawReal_trace]
  dsimp only [H, C, D]
  ring

theorem oneOneNorm (h : HermitianField M) : Blueprint.PaperOneOneNormNormalization h := by
  intro A hA x
  rw [formNormSq, formInner_oneOne h A A hA hA x]
  simp only [pow_two, Matrix.mul_assoc]

end Yau.NodeProofs.G04Aux
