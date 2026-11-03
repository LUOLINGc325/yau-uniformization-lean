import Yau.Proofs.C01WirtingerProducts

/-! Jacobi's determinant derivative for the actual metric jets.
The elementary multilinear proof follows the canonical MatrixCalculus
section of `Yau.LeafProofs.L07` at A e0dbe0df; it is proved in this own
consumer, without importing L07 or any of its geometric dependencies. -/

noncomputable section

open scoped Topology ContDiff Matrix

namespace Yau.NodeProofs.C01Aux

open Yau

variable {r : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def determinantMultilinear (r : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin r => Fin r → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

theorem determinantMultilinear_apply (A : Matrix (Fin r) (Fin r) ℂ) :
    determinantMultilinear r A = A.det := rfl

theorem determinant_linearDeriv (A D : Matrix (Fin r) (Fin r) ℂ) :
    (determinantMultilinear r).linearDeriv A D =
      ∑ i, (A.updateRow i (D i)).det := by
  exact (determinantMultilinear r).linearDeriv_apply A D

theorem determinant_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) :
    fderiv ℝ (fun w => (H w).det) z v =
      ∑ i, ((H z).updateRow i (fderiv ℝ H z v i)).det := by
  have hd := (((determinantMultilinear r).hasFDerivAt (H z)).restrictScalars ℝ).comp
    z hH.hasFDerivAt
  calc
    _ = (determinantMultilinear r).linearDeriv (H z) (fderiv ℝ H z v) :=
      congrArg (fun f : X →L[ℝ] ℂ => f v) hd.fderiv
    _ = _ := determinant_linearDeriv (H z) (fderiv ℝ H z v)

theorem determinant_updateRow_of_invertible (A D : Matrix (Fin r) (Fin r) ℂ)
    (hA : IsUnit A.det) (i : Fin r) :
    (A.updateRow i (D i)).det = (D * A⁻¹) i i * A.det := by
  have heq : ∑ j, (D * A⁻¹) i j • A j = D i := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change ((D * A⁻¹) * A) i k = D i k
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  rw [← heq, Matrix.det_updateRow_sum, smul_eq_mul]

theorem determinant_fderiv_trace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    fderiv ℝ (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ * fderiv ℝ H z v) := by
  rw [determinant_fderiv H z v hH]
  simp_rw [determinant_updateRow_of_invertible (H z) _ hdet]
  rw [← Finset.sum_mul]
  change Matrix.trace (fderiv ℝ H z v * (H z)⁻¹) * (H z).det = _
  rw [Matrix.trace_mul_comm, mul_comm]

theorem matrix_fderiv_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (i j : Fin r) :
    fderiv ℝ (fun w => H w i j) z v = fderiv ℝ H z v i j := by
  have hrow : DifferentiableAt ℝ (fun w => H w i) z :=
    (differentiableAt_pi.mp hH) i
  have h₁ := congrArg (fun L : X →L[ℝ] ℂ => L v) (fderiv_apply hrow j)
  have h₂ := congrArg (fun L : X →L[ℝ] (Fin r → ℂ) => L v j) (fderiv_apply hH i)
  exact h₁.trans h₂

theorem matrix_wirt_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) :
    (Matrix.of fun i j => wirt (fun w => H w i j) z v) =
      (1 / 2 : ℂ) • (fderiv ℝ H z v - Complex.I • fderiv ℝ H z (Complex.I • v)) := by
  ext i j
  simp only [wirt, matrix_fderiv_entry H z _ hH, Matrix.of_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

theorem determinant_wirt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    wirt (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirt (fun w => H w i j) z v)) := by
  rw [matrix_wirt_eq H z v hH]
  simp only [wirt, determinant_fderiv_trace H z _ hH hdet, Matrix.mul_smul,
    Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  ring

theorem determinant_wirtBar {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → Matrix (Fin r) (Fin r) ℂ) (z v : X)
    (hH : DifferentiableAt ℝ H z) (hdet : IsUnit (H z).det) :
    wirtBar (fun w => (H w).det) z v =
      (H z).det * Matrix.trace ((H z)⁻¹ *
        (Matrix.of fun i j => wirtBar (fun w => H w i j) z v)) := by
  have hmat : (Matrix.of fun i j => wirtBar (fun w => H w i j) z v) =
      (1 / 2 : ℂ) • (fderiv ℝ H z v + Complex.I • fderiv ℝ H z (Complex.I • v)) := by
    ext i j
    simp only [wirtBar, matrix_fderiv_entry H z _ hH, Matrix.of_apply,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  rw [hmat]
  simp only [wirtBar, determinant_fderiv_trace H z _ hH hdet, Matrix.mul_smul,
    Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  ring

/-- A holomorphic scalar outer map acts on both actual Wirtinger jets,
even when the inner map is only real differentiable. -/
theorem scalar_holomorphic_outer_wirtinger
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : V → ℂ) (g : ℂ → ℂ) (z v : V) (a : ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : HasDerivAt g a (f z)) :
    wirt (fun p => g (f p)) z v = a * wirt f z v ∧
      wirtBar (fun p => g (f p)) z v = a * wirtBar f z v := by
  have hd := (hg.hasFDerivAt.restrictScalars ℝ).comp z hf.hasFDerivAt
  have hdf := hd.fderiv
  simp only [Function.comp_def] at hdf
  constructor
  · unfold wirt
    rw [hdf]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  · unfold wirtBar
    rw [hdf]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring

end Yau.NodeProofs.C01Aux
