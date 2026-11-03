import Yau.Proofs.V03HolomorphicSmooth
import Yau.Proofs.U02AnalyticBounds
import Yau.Blueprint.Alignment

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Set
open scoped ContDiff BigOperators

variable {n : ℕ}

def jacobianMatrix (A : ComplexVector n →L[ℂ] ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A (stdVec j) i

theorem jacobianMatrix_det (A : ComplexVector n →L[ℂ] ComplexVector n) :
    (jacobianMatrix A).det = LinearMap.det A.toLinearMap := by
  have h : jacobianMatrix A = LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis A.toLinearMap := by
    ext i j
    simp [jacobianMatrix, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply, stdVec]
  rw [h, LinearMap.det_toMatrix]

theorem norm_jacobianMatrix_entry (A : ComplexVector n →L[ℂ] ComplexVector n)
    (i j : Fin n) : ‖jacobianMatrix A i j‖ ≤ ‖A‖ := by
  apply (PiLp.norm_apply_le (A (stdVec j)) i).trans
  have hj : ‖stdVec j‖ = 1 := by
    change ‖(PiLp.single 2 j (1 : ℂ) : ComplexVector n)‖ = 1
    simp
  simpa only [hj, mul_one] using A.le_opNorm (stdVec j)

theorem norm_linearMap_det_le (A : ComplexVector n →L[ℂ] ComplexVector n) :
    ‖LinearMap.det A.toLinearMap‖ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ‖A‖ ^ n := by
  rw [← jacobianMatrix_det, Matrix.det_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ‖A‖ ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_units_zsmul, norm_prod]
      exact (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        (fun i _ => norm_jacobianMatrix_entry A (σ i) i)).trans (by simp)
    _ = _ := by simp

theorem differentiableOn_jacobian_det {O : Set (ComplexVector n)} (hO : IsOpen O)
    {f : ComplexVector n → ComplexVector n} (hf : DifferentiableOn ℂ f O) :
    DifferentiableOn ℂ (fun z => LinearMap.det (fderiv ℂ f z).toLinearMap) O := by
  have hC := Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn hO hf
  have hD : DifferentiableOn ℂ (fderiv ℂ f) O :=
    (hC.fderiv_of_isOpen hO (m := 1) (by simp)).differentiableOn (by norm_num)
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => jacobianMatrix (fderiv ℂ f z) i j) O := by
    exact (EuclideanSpace.proj i).differentiable.comp_differentiableOn
      (hD.clm_apply (differentiableOn_const (stdVec j)))
  have hprod (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
      DifferentiableOn ℂ (fun z => ∏ i ∈ S, jacobianMatrix (fderiv ℂ f z) (σ i) i) O := by
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (differentiableOn_const (1 : ℂ) : DifferentiableOn ℂ
        (fun _ : ComplexVector n => (1 : ℂ)) O)
    | @insert j S hj hS =>
      simp only [Finset.prod_insert hj]
      convert! (hentry (σ j) j).mul hS using 1
  have hdet : (fun z => LinearMap.det (fderiv ℂ f z).toLinearMap) =
      fun z => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ i, jacobianMatrix (fderiv ℂ f z) (σ i) i := by
    funext z
    rw [← jacobianMatrix_det, Matrix.det_apply']
  rw [hdet]
  exact DifferentiableOn.fun_sum fun σ _ => (hprod σ Finset.univ).const_mul _

theorem jacobian_det_ne_zero {A : ComplexVector n →L[ℂ] ComplexVector n}
    (hA : Function.Bijective A) : LinearMap.det A.toLinearMap ≠ 0 := by
  exact (LinearEquiv.ofBijective A.toLinearMap hA).isUnit_det'.ne_zero

end Yau.Proofs.Y05Aux
