import Yau.Proofs.E02TangentMixed

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Exact sum of the two real log-Gram second-derivative expressions.
The matrix B is arbitrary here; no spectral basis is chosen. -/
theorem gram_log_hessian_complex_sum {n m : ℕ} (M Z : Rect n m) (B : Herm n) :
    (B*(Z*Zᴴ+Z*Zᴴ)-B*(M*Zᴴ+Z*Mᴴ)*B*(M*Zᴴ+Z*Mᴴ))+
      (B*((Complex.I • Z)*(Complex.I • Z)ᴴ+(Complex.I • Z)*(Complex.I • Z)ᴴ)-
        B*(M*(Complex.I • Z)ᴴ+(Complex.I • Z)*Mᴴ)*B*
          (M*(Complex.I • Z)ᴴ+(Complex.I • Z)*Mᴴ)) =
      (4 : ℂ) • (B*Z*Zᴴ)-(2 : ℂ) •
        (B*M*Zᴴ*B*Z*Mᴴ+B*Z*Mᴴ*B*M*Zᴴ) := by
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_I,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.mul_smul,smul_add,smul_sub,smul_smul,
    smul_neg,neg_smul,Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc,Complex.I_mul_I]
  module

theorem gram_log_hessian_real_trace {n m : ℕ} (M Z : Rect n m) (B : Herm n) :
    ((Matrix.trace (B*(Z*Zᴴ+Z*Zᴴ)-B*(M*Zᴴ+Z*Mᴴ)*B*(M*Zᴴ+Z*Mᴴ))).re+
      (Matrix.trace (B*((Complex.I • Z)*(Complex.I • Z)ᴴ+(Complex.I • Z)*(Complex.I • Z)ᴴ)-
        B*(M*(Complex.I • Z)ᴴ+(Complex.I • Z)*Mᴴ)*B*
          (M*(Complex.I • Z)ᴴ+(Complex.I • Z)*Mᴴ))).re)/4 =
      (Matrix.trace (B*Z*Zᴴ-B*Z*Mᴴ*B*M*Zᴴ)).re := by
  have h := congrArg (fun A : Herm n => (Matrix.trace A).re) (gram_log_hessian_complex_sum M Z B)
  have hCycle : Matrix.trace (B*M*Zᴴ*B*Z*Mᴴ) = Matrix.trace (B*Z*Mᴴ*B*M*Zᴴ) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B*M*Zᴴ) (B*Z*Mᴴ)
  simp only [Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
    Complex.add_re,Complex.sub_re,Complex.mul_re,
    zero_mul,sub_zero,hCycle] at h ⊢
  norm_num at h ⊢
  linarith

/-- The remaining real trace is the nonnegative square norm of the
actual tangent S. This is the constant-one rectangular logdet identity. -/
theorem trace_projectorTangent_mul_adjoint {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    Matrix.trace (projectorTangent M Z*(projectorTangent M Z)ᴴ) =
      Matrix.trace ((M*Mᴴ)⁻¹*Z*(1-rowProjector M)*Zᴴ) := by
  rw [Matrix.trace_mul_comm,projectorTangent_adjoint_mul_self M Z hM]
  calc
    _ = Matrix.trace ((Zᴴ*(M*Mᴴ)⁻¹*Z*(1-rowProjector M))*(1-rowProjector M)) := by
      have hCycle := Matrix.trace_mul_comm (m := Fin m) (n := Fin m) (R := ℂ)
        (1-rowProjector M) (Zᴴ*(M*Mᴴ)⁻¹*Z*(1-rowProjector M))
      simpa only [Matrix.mul_assoc] using hCycle
    _ = Matrix.trace (Zᴴ*(M*Mᴴ)⁻¹*Z*(1-rowProjector M)) := by
      rw [Matrix.mul_assoc,one_sub_rowProjector_idempotent M hM]
    _ = _ := by
      let R : Rect n m := (M*Mᴴ)⁻¹*Z*(1-rowProjector M)
      have hCycle : Matrix.trace (Zᴴ*R) = Matrix.trace (R*Zᴴ) :=
        Matrix.trace_mul_comm (m := Fin m) (n := Fin n) (R := ℂ) Zᴴ R
      simpa only [R,Matrix.mul_assoc] using hCycle

theorem gram_log_hessian_trace_eq_tangent {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    ((Matrix.trace ((M*Mᴴ)⁻¹*(Z*Zᴴ+Z*Zᴴ)-
        (M*Mᴴ)⁻¹*(M*Zᴴ+Z*Mᴴ)*(M*Mᴴ)⁻¹*(M*Zᴴ+Z*Mᴴ))).re+
      (Matrix.trace ((M*Mᴴ)⁻¹*((Complex.I • Z)*(Complex.I • Z)ᴴ+(Complex.I • Z)*(Complex.I • Z)ᴴ)-
        (M*Mᴴ)⁻¹*(M*(Complex.I • Z)ᴴ+(Complex.I • Z)*Mᴴ)*(M*Mᴴ)⁻¹*
          (M*(Complex.I • Z)ᴴ+(Complex.I • Z)*Mᴴ))).re)/4 =
      (Matrix.trace (projectorTangent M Z*(projectorTangent M Z)ᴴ)).re := by
  rw [gram_log_hessian_real_trace,trace_projectorTangent_mul_adjoint M Z hM]
  congr 2
  unfold rowProjector
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]

end Yau.NodeProofs.E02Aux
