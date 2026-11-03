import Yau.Proofs.F01QuadraticWirtingerJet

/-! The actual Jacobian of any C2 holomorphic coordinate map has symmetric
first complex coordinate jets. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem holomorphic_jacobian_entry_differentiableAt
    {T : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hT : ContDiffAt ℂ 2 T z) (i j : Fin n) :
    DifferentiableAt ℂ (fun w => linearMatrix (fderiv ℂ T w) i j) z := by
  have hD : ContDiffAt ℂ 1 (fderiv ℂ T) z := hT.fderiv_right (by norm_num)
  exact (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiableAt.comp z
    (hD.differentiableAt one_ne_zero |>.clm_apply (differentiableAt_const (stdVec j)))

theorem holomorphic_jacobian_entry_wirt
    {T : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hT : ContDiffAt ℂ 2 T z) (v : ComplexVector n) (i j : Fin n) :
    wirt (fun w => linearMatrix (fderiv ℂ T w) i j) z v =
      fderiv ℂ (fderiv ℂ T) z v (stdVec j) i := by
  rw [wirt_of_complex_differentiable (holomorphic_jacobian_entry_differentiableAt hT i j)]
  have hD : DifferentiableAt ℂ (fderiv ℂ T) z :=
    (hT.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv ℂ ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ) ∘
    (fun w => fderiv ℂ T w (stdVec j))) z v = _
  rw [fderiv_comp z (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiableAt
    (hD.clm_apply (differentiableAt_const (stdVec j))), ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.proj, PiLp.proj_apply]
  rw [fderiv_clm_apply hD (differentiableAt_const (stdVec j))]
  have hc : fderiv ℂ (fun _ : ComplexVector n => stdVec j) z = 0 :=
    (hasFDerivAt_const (stdVec j) z).fderiv
  rw [hc]
  simp

theorem holomorphic_jacobian_wirt_symm
    {T : ComplexVector n → ComplexVector n} {z : ComplexVector n}
    (hT : ContDiffAt ℂ 2 T z) (i j k : Fin n) :
    wirt (fun w => linearMatrix (fderiv ℂ T w) i j) z (stdVec k) =
      wirt (fun w => linearMatrix (fderiv ℂ T w) i k) z (stdVec j) := by
  rw [holomorphic_jacobian_entry_wirt hT, holomorphic_jacobian_entry_wirt hT]
  exact congrArg (fun u : ComplexVector n => u i)
    (hT.isSymmSndFDerivAt (by norm_num) (stdVec k) (stdVec j))

end Yau.NodeProofs.F01Aux
