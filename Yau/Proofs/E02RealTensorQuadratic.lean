import Yau.Proofs.E02RealTensorLevi
import Yau.Proofs.E02PolynomialJet
import Yau.Proofs.E02HermitianQuadratic

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [Fintype ι]

/-- Symmetry of the genuine Peano tensor gives its literal Hermitian
complex matrix. No derivative field of the Peano function is used. -/
theorem realTensorLevi_affine_isHermitian (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (L : F →L[ℝ] E) (dir : ι → F) :
    (realTensorLevi A (fun i => L (dir i)) (fun i => L (Complex.I • dir i))).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  apply Complex.ext <;> simp only [realTensorLevi,Complex.star_def,Complex.conj_re,Complex.conj_im]
  · rw [hA (L (dir i)) (L (dir j)),hA (L (Complex.I • dir i)) (L (Complex.I • dir j))]
  · rw [hA (L (dir i)) (L (Complex.I • dir j)),hA (L (Complex.I • dir i)) (L (dir j))]
    ring

/-- The actual complex quadratic form of a Peano tensor is precisely
the quarter-sum in the two packed real spatial directions. -/
theorem realTensorLevi_affine_quadratic (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (L : F →L[ℝ] E) (dir : ι → F) (v : ι → ℂ) :
    (star v ⬝ᵥ (realTensorLevi A (fun i => L (dir i))
        (fun i => L (Complex.I • dir i))*ᵥv)).re =
      (A (L (complexDirectionCombination dir v)) (L (complexDirectionCombination dir v))+
        A (L (Complex.I • complexDirectionCombination dir v))
          (L (Complex.I • complexDirectionCombination dir v)))/4 := by
  let f : E → ℝ := jetPolynomial 0 0 0 A
  have hf : ContDiffAt ℝ 2 f (0+L 0) :=
    (jetPolynomial_contDiff 0 0 0 A).contDiffAt.of_le (by simp)
  have hLevi := leviMatrix_real_affine (0 : E) L hf dir
  rw [jetPolynomial_second_fderiv 0 0 0 A hA] at hLevi
  have hPull := affinePullback_second_fderiv (0 : E) L hf
  rw [jetPolynomial_second_fderiv 0 0 0 A hA] at hPull
  have hComp : ContDiffAt ℝ 2 (fun y => f (0+L y)) (0 : F) :=
    hf.comp 0 (contDiff_const.add L.contDiff).contDiffAt
  have hQ := leviMatrix_quadratic_re hComp dir v
  rw [hLevi,hPull] at hQ
  exact hQ

theorem realTensorLevi_affine_order (A B : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (hB : ∀ v w, B v w = B w v)
    (hOrder : ∀ v, A v v ≤ B v v) (L : F →L[ℝ] E) (dir : ι → F) :
    (realTensorLevi B (fun i => L (dir i)) (fun i => L (Complex.I • dir i))-
      realTensorLevi A (fun i => L (dir i)) (fun i => L (Complex.I • dir i))).PosSemidef := by
  apply (hermitian_posSemidef_iff_re_quadratic_nonneg _
    ((realTensorLevi_affine_isHermitian B hB L dir).sub
      (realTensorLevi_affine_isHermitian A hA L dir))).mpr
  intro v
  rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,
    realTensorLevi_affine_quadratic B hB L dir v,realTensorLevi_affine_quadratic A hA L dir v]
  linarith [hOrder (L (complexDirectionCombination dir v)),
    hOrder (L (Complex.I • complexDirectionCombination dir v))]

end Yau.NodeProofs.E02Aux
