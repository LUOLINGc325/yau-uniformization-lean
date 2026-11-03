import Yau.Proofs.E02ProjectorFirst

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rectEntryLinear (n m : ℕ) (i : Fin n) (j : Fin m) : Rect n m →ₗ[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rectEntryCLM (n m : ℕ) (i : Fin n) (j : Fin m) : Rect n m →L[ℝ] ℂ :=
  (rectEntryLinear n m i j).mkContinuous 1 (fun A => by
    change ‖A i j‖ ≤ 1*‖A‖
    simpa only [one_mul] using
      Matrix.norm_entry_le_entrywise_sup_norm (A := A) (i := i) (j := j))

theorem fderiv_matrix_entry {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n m : ℕ} (F : D → Rect n m) (x v : D) (hF : DifferentiableAt ℝ F x)
    (i : Fin n) (j : Fin m) :
    fderiv ℝ (fun y => F y i j) x v = fderiv ℝ F x v i j := by
  have h := (rectEntryCLM n m i j).hasFDerivAt.comp x hF.hasFDerivAt
  exact congrArg (fun L : D →L[ℝ] ℂ => L v) h.fderiv

/-- The actual entrywise Wirtinger derivative of the explicit projector
is S, obtained from the two real directional derivatives. -/
theorem rowProjector_wirt_of_inverseGram {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M)
    (i j : Fin m) :
    wirt (fun N : Rect n m => rowProjector N i j) M Z = projectorTangent M Z i j := by
  have hP := rowProjector_differentiableAt_of_inverseGram M hInv
  have hZ := congrArg (fun A : Herm m => A i j)
    (rowProjector_fderiv_apply_of_inverseGram M Z hM hInv)
  have hIZ := congrArg (fun A : Herm m => A i j)
    (rowProjector_fderiv_apply_of_inverseGram M (Complex.I • Z) hM hInv)
  rw [wirt,fderiv_matrix_entry _ M Z hP i j,
    fderiv_matrix_entry _ M (Complex.I • Z) hP i j]
  erw [hZ,hIZ]
  rw [projectorTangent_smul_direction,Matrix.conjTranspose_smul]
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.neg_apply,smul_eq_mul,Complex.star_def,
    Complex.conj_I,neg_smul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The actual barred Wirtinger derivative is the adjoint Sᴴ. -/
theorem rowProjector_wirtBar_of_inverseGram {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M)
    (i j : Fin m) :
    wirtBar (fun N : Rect n m => rowProjector N i j) M Z = (projectorTangent M Z)ᴴ i j := by
  have hP := rowProjector_differentiableAt_of_inverseGram M hInv
  have hZ := congrArg (fun A : Herm m => A i j)
    (rowProjector_fderiv_apply_of_inverseGram M Z hM hInv)
  have hIZ := congrArg (fun A : Herm m => A i j)
    (rowProjector_fderiv_apply_of_inverseGram M (Complex.I • Z) hM hInv)
  rw [wirtBar,fderiv_matrix_entry _ M Z hP i j,
    fderiv_matrix_entry _ M (Complex.I • Z) hP i j]
  erw [hZ,hIZ]
  rw [projectorTangent_smul_direction,Matrix.conjTranspose_smul]
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.neg_apply,smul_eq_mul,Complex.star_def,
    Complex.conj_I,neg_smul]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Yau.NodeProofs.E02Aux
