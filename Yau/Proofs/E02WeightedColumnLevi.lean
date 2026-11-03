import Yau.Proofs.E02ColumnLevi

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qform_real_smul {n : ℕ} (B : Herm n) (V : ComplexVector n) (r : ℝ) :
    qform B ((r : ℂ) • V) = r^2*qform B V := by
  have hv : WithLp.ofLp ((r : ℂ) • V) = (r : ℂ) • WithLp.ofLp V := rfl
  simp only [qform,hv,star_smul,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,Complex.star_def,Complex.conj_ofReal,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
  ring

theorem rowProjector_diag_quadratic {n m : ℕ} (M : Rect n m) (j : Fin m) :
    rowProjector M j j =
      star (fun a => M a j) ⬝ᵥ ((M*Mᴴ)⁻¹*ᵥ(fun a => M a j)) := by
  rw [rowProjector,Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,dotProduct,Matrix.mulVec,
    Pi.star_apply]

theorem rowProjector_weighted_diag {n m : ℕ} (α : Fin m → ℝ)
    (η : Fin m → ComplexVector n) (hα : ∀ i, 0 ≤ α i) (j : Fin m) :
    (rowProjector (weightedColumns α η) j j).re =
      α j*qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) (η j) := by
  rw [rowProjector_diag_quadratic]
  change qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹)
    ((Real.sqrt (α j) : ℂ) • η j) = _
  rw [qform_real_smul,Real.sq_sqrt (hα j)]

/-- The exact vertical-column Levi, retaining its positive contact
weight until the later vertical comparison explicitly cancels it. -/
theorem logGram_rectLevi_weightedColumn {n m : ℕ} (α : Fin m → ℝ)
    (η : Fin m → ComplexVector n) (hα : ∀ i, 0 ≤ α i)
    (hM : (weightedColumns α η*(weightedColumns α η)ᴴ).PosDef)
    (j : Fin m) (V : ComplexVector n) :
    rectLevi logGram (weightedColumns α η)
        (singleColumn j ((Real.sqrt (α j) : ℂ) • V)) =
      α j*(1-α j*qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) (η j))*
        qform ((weightedColumns α η*(weightedColumns α η)ᴴ)⁻¹) V := by
  rw [logGram_rectLevi_singleColumn _ hM,rowProjector_weighted_diag α η hα,
    qform_real_smul,Real.sq_sqrt (hα j)]
  ring

end Yau.NodeProofs.E02Aux
