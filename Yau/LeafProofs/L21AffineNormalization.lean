import Yau.LeafProofs.L21LinearNormalization
import Yau.LeafProofs.L21GraphAlgebra

/-! Affine transport of the original complex structure and Nijenhuis tensor. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def rescalePoint (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ) (z : X n) : X n :=
  p + r • S.symm z

def rescaleInverse (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ) (x : X n) : X n :=
  r⁻¹ • S (x - p)

theorem rescaleInverse_rescalePoint (p : X n) (S : X n ≃L[ℝ] X n)
    {r : ℝ} (hr : r ≠ 0) (z : X n) :
    rescaleInverse p S r (rescalePoint p S r z) = z := by
  simp [rescaleInverse, rescalePoint, map_smul, smul_smul, hr]

theorem rescalePoint_rescaleInverse (p : X n) (S : X n ≃L[ℝ] X n)
    {r : ℝ} (hr : r ≠ 0) (x : X n) :
    rescalePoint p S r (rescaleInverse p S r x) = x := by
  simp [rescaleInverse, rescalePoint, map_smul, smul_smul, hr]

theorem contDiff_rescalePoint (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ) :
    ContDiff ℝ ∞ (rescalePoint p S r) :=
  contDiff_const.add ((S.symm.contDiff : ContDiff ℝ ∞ S.symm).const_smul r)

theorem hasFDerivAt_rescalePoint (p : X n) (S : X n ≃L[ℝ] X n)
    (r : ℝ) (z : X n) :
    HasFDerivAt (rescalePoint p S r) (r • S.symm.toContinuousLinearMap) z :=
  ((S.symm.toContinuousLinearMap.hasFDerivAt).const_smul r).const_add p

def rescaleStructure (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    (J : X n → X n →L[ℝ] X n) (z : X n) : X n →L[ℝ] X n :=
  S.toContinuousLinearMap.comp ((J (rescalePoint p S r z)).comp S.symm.toContinuousLinearMap)

@[simp] theorem rescaleStructure_apply (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    (J : X n → X n →L[ℝ] X n) (z v : X n) :
    rescaleStructure p S r J z v = S (J (rescalePoint p S r z) (S.symm v)) := rfl

theorem rescaleStructure_square (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    (J : X n → X n →L[ℝ] X n) (z : X n)
    (hJ2 : ∀ v, J (rescalePoint p S r z) (J (rescalePoint p S r z) v) = -v)
    (v : X n) :
    rescaleStructure p S r J z (rescaleStructure p S r J z v) = -v := by
  simp [hJ2]

theorem differentiableAt_rescaleStructure (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    {J : X n → X n →L[ℝ] X n} {z : X n}
    (hJ : DifferentiableAt ℝ J (rescalePoint p S r z)) :
    DifferentiableAt ℝ (rescaleStructure p S r J) z := by
  exact (differentiableAt_const S.toContinuousLinearMap).clm_comp
    ((hJ.comp z (hasFDerivAt_rescalePoint p S r z).differentiableAt).clm_comp
      (differentiableAt_const S.symm.toContinuousLinearMap))

theorem contDiffAt_rescaleStructure (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    {J : X n → X n →L[ℝ] X n} {z : X n}
    (hJ : ContDiffAt ℝ ∞ J (rescalePoint p S r z)) :
    ContDiffAt ℝ ∞ (rescaleStructure p S r J) z := by
  exact contDiffAt_const.clm_comp
    ((hJ.comp z (contDiff_rescalePoint p S r).contDiffAt).clm_comp contDiffAt_const)

theorem fderiv_rescaleStructure (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    {J : X n → X n →L[ℝ] X n} {z : X n}
    (hJ : DifferentiableAt ℝ J (rescalePoint p S r z)) (u v : X n) :
    fderiv ℝ (rescaleStructure p S r J) z u v =
      r • S (fderiv ℝ J (rescalePoint p S r z) (S.symm u) (S.symm v)) := by
  have hd : HasFDerivAt (fun y => J y (S.symm v))
      (fderiv ℝ J (rescalePoint p S r z) |>.flip (S.symm v))
      (rescalePoint p S r z) := by
    rw [← fderiv_structure_apply_const hJ]
    exact (hJ.clm_apply (differentiableAt_const (S.symm v))).hasFDerivAt
  have he := S.toContinuousLinearMap.hasFDerivAt.comp z
    (hd.comp z (hasFDerivAt_rescalePoint p S r z))
  have he' := congrArg (fun L : X n →L[ℝ] X n => L u) he.fderiv
  change fderiv ℝ (fun y => rescaleStructure p S r J y v) z u = _ at he'
  rw [fderiv_structure_apply_const (differentiableAt_rescaleStructure p S r hJ)] at he'
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, ContinuousLinearEquiv.coe_coe, map_smul] using he'

/-- Exact affine covariance of the frozen tensor, including the scale factor. -/
theorem nijenhuis_rescaleStructure (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    {J : X n → X n →L[ℝ] X n} {z : X n}
    (hJ : DifferentiableAt ℝ J (rescalePoint p S r z)) (v w : X n) :
    Yau.LeafCandidates.nijenhuis (rescaleStructure p S r J) z v w =
      r • S (Yau.LeafCandidates.nijenhuis J (rescalePoint p S r z) (S.symm v) (S.symm w)) := by
  rw [nijenhuis_eq_tensor (differentiableAt_rescaleStructure p S r hJ),
    nijenhuis_eq_tensor hJ]
  simp only [fderiv_rescaleStructure p S r hJ, rescaleStructure_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_smul, map_add, map_sub,
    smul_add, smul_sub]

theorem rescaleStructure_at_zero (p : X n) (S : X n ≃L[ℝ] X n) (r : ℝ)
    (J : X n → X n →L[ℝ] X n)
    (hS : ∀ v, S (J p v) = Complex.I • S v) (v : X n) :
    rescaleStructure p S r J 0 v = Complex.I • v := by
  simp [rescaleStructure_apply, rescalePoint, hS]

end Yau.LeafProofs.L21Aux
