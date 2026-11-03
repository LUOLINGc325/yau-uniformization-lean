import Yau.Geometry.HolomorphicBundle

noncomputable section
open scoped ContDiff

namespace Yau.LeafProofs.L14Aux

theorem wirt_eq_fderiv_of_complex_differentiable {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (f : X → ℂ) (z v : X)
    (hf : DifferentiableAt ℂ f z) :
    wirt f z v = fderiv ℂ f z v := by
  unfold wirt
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) * (fderiv ℂ f z v - Complex.I * fderiv ℂ f z (Complex.I • v)) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

theorem wirtBar_conjugate_of_complex_differentiable {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (f : X → ℂ) (z v : X)
    (hf : DifferentiableAt ℂ f z) :
    wirtBar (fun y => star (f y)) z v = star (fderiv ℂ f z v) := by
  have hconj : wirtBar (fun y => star (f y)) z v = star (wirt f z v) := by
    unfold wirtBar wirt
    rw [fderiv_star]
    simp [star_mul, star_sub, Complex.star_def]
    ring
  rw [hconj, wirt_eq_fderiv_of_complex_differentiable f z v hf]

theorem conjugate_jacobian_wirtBar_symm {n : ℕ}
    (T : ComplexVector n → ComplexVector n) (z : ComplexVector n)
    (hT : ContDiffAt ℂ 2 T z) (i j k : Fin n) :
    wirtBar (fun y => star (fderiv ℂ T y (stdVec j) i)) z (stdVec k) =
      wirtBar (fun y => star (fderiv ℂ T y (stdVec k) i)) z (stdVec j) := by
  have hD : DifferentiableAt ℂ (fderiv ℂ T) z :=
    (hT.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd (p : Fin n) : DifferentiableAt ℂ (fun y => fderiv ℂ T y (stdVec p) i) z :=
    (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).differentiableAt.comp z
      (hD.clm_apply (differentiableAt_const (stdVec p)))
  rw [wirtBar_conjugate_of_complex_differentiable _ z _ (hd j),
    wirtBar_conjugate_of_complex_differentiable _ z _ (hd k)]
  congr 1
  have hs := hT.isSymmSndFDerivAt (by norm_num)
  have he := hs (stdVec k) (stdVec j)
  have hcoord (p : Fin n) : fderiv ℂ (fun y => fderiv ℂ T y (stdVec p) i) z =
      (EuclideanSpace.proj i).comp (fderiv ℂ (fun y => fderiv ℂ T y (stdVec p)) z) :=
    ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).hasFDerivAt.comp z
      (hD.clm_apply (differentiableAt_const (stdVec p))).hasFDerivAt).fderiv
  rw [hcoord j, hcoord k, fderiv_clm_apply hD (differentiableAt_const _),
    fderiv_clm_apply hD (differentiableAt_const _)]
  simpa using congrArg (fun v : ComplexVector n => v i) he

end Yau.LeafProofs.L14Aux
