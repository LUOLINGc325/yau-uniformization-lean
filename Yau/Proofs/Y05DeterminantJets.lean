import Yau.Proofs.Y05Jacobian
import Yau.Proofs.Y05JetOperations

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment
open scoped ContDiff

variable {n d : ℕ}

theorem contDiff_linearMap_det : ContDiff ℂ ∞
    (fun A : ComplexVector n →L[ℂ] ComplexVector n => LinearMap.det A.toLinearMap) := by
  have hentry (i j : Fin n) : ContDiff ℂ ∞
      (fun A : ComplexVector n →L[ℂ] ComplexVector n => jacobianMatrix A i j) := by
    have hA : ContDiff ℂ ∞ (fun A : ComplexVector n →L[ℂ] ComplexVector n => A (stdVec j)) :=
      (contDiff_id : ContDiff ℂ ∞ (id : (ComplexVector n →L[ℂ] ComplexVector n) →
        (ComplexVector n →L[ℂ] ComplexVector n))).clm_apply contDiff_const
    convert! (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).contDiff.comp hA using 1
  have hprod (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ContDiff ℂ ∞
      (fun A : ComplexVector n →L[ℂ] ComplexVector n => ∏ i ∈ S, jacobianMatrix A (σ i) i) := by
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℂ ∞
        (fun _ : ComplexVector n →L[ℂ] ComplexVector n => (1 : ℂ)))
    | @insert i S hi hS =>
      simp only [Finset.prod_insert hi]
      convert! (hentry (σ i) i).mul hS using 1
  have hdet : (fun A : ComplexVector n →L[ℂ] ComplexVector n => LinearMap.det A.toLinearMap) =
      fun A => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, jacobianMatrix A (σ i) i := by
    funext A
    rw [← jacobianMatrix_det, Matrix.det_apply']
  rw [hdet]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (hprod σ Finset.univ)

theorem iteratedFDeriv_fderiv_congr {f g : ComplexVector n → ComplexVector n}
    (h : GermJetEq f g d) {m : ℕ} (hm : m + 1 ≤ d) :
    iteratedFDeriv ℂ m (fderiv ℂ f) 0 = iteratedFDeriv ℂ m (fderiv ℂ g) 0 := by
  ext v w i
  have H := congrArg (fun L => L (Fin.snoc v w)) (h (m + 1) hm)
  simpa only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last] using
    congrArg (fun z : ComplexVector n => z i) H

/-- Agreement through order `d` controls the actual Jacobian determinant
through order `d-1`, including every mixed Fréchet derivative. -/
theorem germJetEq_jacobian_det {f g : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0)
    (h : GermJetEq f g d) :
    ScalarJetEq (fun z => LinearMap.det (fderiv ℂ f z).toLinearMap)
      (fun z => LinearMap.det (fderiv ℂ g z).toLinearMap) (d - 1) := by
  have hFDf : ContDiffAt ℂ (d - 1 : ℕ) (fderiv ℂ f) 0 :=
    hf.fderiv_right (by exact_mod_cast (show d - 1 + 1 ≤ d by omega))
  have hFDg : ContDiffAt ℂ (d - 1 : ℕ) (fderiv ℂ g) 0 :=
    hg.fderiv_right (by exact_mod_cast (show d - 1 + 1 ≤ d by omega))
  have hFD0 : fderiv ℂ f 0 = fderiv ℂ g 0 := by
    have H := iteratedFDeriv_fderiv_congr h (m := 0) (by simpa using hd)
    have H' := congrArg (fun L => L (fun i : Fin 0 => Fin.elim0 i)) H
    simpa only [iteratedFDeriv_zero_apply] using H'
  exact iteratedFDeriv_comp_congr_at (f := fderiv ℂ f) (f' := fderiv ℂ g)
    (g := fun A : ComplexVector n →L[ℂ] ComplexVector n => LinearMap.det A.toLinearMap)
    (g' := fun A : ComplexVector n →L[ℂ] ComplexVector n => LinearMap.det A.toLinearMap)
    hFDf hFDg
    ((contDiff_linearMap_det (n := n)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((contDiff_linearMap_det (n := n)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (fun m hm => iteratedFDeriv_fderiv_congr (m := m) h (by omega))
    (fun m hm => by simpa only [hFD0])

end Yau.Proofs.Y05Aux
