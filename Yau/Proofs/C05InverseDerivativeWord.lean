import Yau.Proofs.C05LoweredInverseDerivative
import Yau.Proofs.C05MetricInverseBound
import Yau.Proofs.C05IntrinsicTensorNorm
import Yau.LeafProofs.L23ContractionWordCalculus
import Yau.LeafProofs.L23ContractionWordNorm

/-! The actual inverse-form derivative is a two-trace tensor word in
two lowered inverse factors and the actual form derivative. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def inverseCompositionWord : Word2 4 3 3 where
  wire :=
    { toFun := Sum.elim
        ![Sum.inl 1, Sum.inr (0, 0), Sum.inr (1, 1), Sum.inl 2]
        ![Sum.inl 0, Sum.inr (0, 1), Sum.inr (1, 0)]
      invFun := Sum.elim ![Sum.inr 0, Sum.inl 0, Sum.inl 3]
        (fun p => if p.1 = 0 then if p.2 = 0 then Sum.inl 1 else Sum.inr 1
          else if p.2 = 0 then Sum.inr 2 else Sum.inl 2)
      left_inv := by
        intro s
        cases s with
        | inl j => fin_cases j <;> rfl
        | inr j => fin_cases j <;> rfl
      right_inv := by
        intro s
        cases s with
        | inl j => fin_cases j <;> rfl
        | inr p => rcases p with ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl }

theorem inverseCompositionWord_eval (H C : Matrix (RIdx n) (RIdx n) ℝ)
    (D : CovTensor n 3) (v : Fin 3 → RIdx n) :
    inverseCompositionWord.eval H
        (tensorConcatProduct (matrixCovTensor C) (matrixCovTensor C)) D v =
      (C * H * (Matrix.of fun a b => D ![v 0, a, b]) * H * C) (v 1) (v 2) := by
  have hL (a b c d : RIdx n) :
      (fun j => Sum.elim v (pairAssignment a b c d)
        (inverseCompositionWord.wire (Sum.inl j))) = ![v 1, a, d, v 2] := by
    funext j
    fin_cases j <;> rfl
  have hR (a b c d : RIdx n) :
      (fun j => Sum.elim v (pairAssignment a b c d)
        (inverseCompositionWord.wire (Sum.inr j))) = ![v 0, b, c] := by
    funext j
    fin_cases j <;> rfl
  rw [Word2.eval_quad]
  simp_rw [hL, hR]
  have hprod (a d : RIdx n) : tensorConcatProduct (matrixCovTensor C) (matrixCovTensor C)
      ![v 1, a, d, v 2] = C (v 1) a * C d (v 2) := rfl
  simp_rw [hprod]
  have hassoc : C * H * (Matrix.of fun a b => D ![v 0, a, b]) * H * C =
      (C * H) * ((Matrix.of fun a b => D ![v 0, a, b]) * (H * C)) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem loweredInverseMatrix_composition (G A B : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.det ≠ 0) :
    loweredInverseMatrix G A * G⁻¹ * B * G⁻¹ * loweredInverseMatrix G A =
      G * A⁻¹ * B * A⁻¹ * G := by
  have hGG := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG)
  have hHG := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG)
  calc
    _ = G * A⁻¹ * (G * G⁻¹) * B * (G⁻¹ * G) * A⁻¹ * G := by
      unfold loweredInverseMatrix
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hGG, hHG]; simp only [Matrix.mul_one]

theorem covariantD_loweredInverse_word (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z)
    (hdet : (A z).det ≠ 0) (v : Fin 3 → RIdx n) :
    covariantD k c (fun w => matrixCovTensor (loweredInverseMatrix (realMetricFn k c w) (A w))) z v =
      -inverseCompositionWord.eval (realMetricFn k c z)⁻¹
        (tensorConcatProduct (matrixCovTensor (loweredInverseMatrix (realMetricFn k c z) (A z)))
          (matrixCovTensor (loweredInverseMatrix (realMetricFn k c z) (A z))))
        (covariantD k c (fun w => matrixCovTensor (A w)) z) v := by
  have hv : v = ![v 0, v 1, v 2] := by funext j; fin_cases j <;> rfl
  have hDA : (Matrix.of fun a b =>
      covariantD k c (fun w => matrixCovTensor (A w)) z ![v 0, a, b]) =
      matrixCovariantD k c A z (v 0) := by
    ext a b
    exact covariantD_matrixCovTensor k c A z (v 0) a b
  rw [inverseCompositionWord_eval, hDA,
    loweredInverseMatrix_composition _ _ _
      (Yau.LeafProofs.L12Aux.realMetricFn_posDef k c z hz).det_pos.ne']
  have hh := covariantD_matrixCovTensor k c
    (fun w => loweredInverseMatrix (realMetricFn k c w) (A w)) z (v 0) (v 1) (v 2)
  rw [matrixCovariantD_loweredInverse k hk c A hz hA hdet (v 0)] at hh
  simpa only [← hv, Matrix.neg_apply] using hh

end Yau.Proofs.C05Aux
