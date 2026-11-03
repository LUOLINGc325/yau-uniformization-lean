import Yau.Proofs.F01BufferedAtlas

/-! Actual invertible complex affine coordinate rescalings. Each chart uses
a nonzero scalar; scale zero occurs only in the smooth coefficient extension. -/
open Set
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

def rescaleHomeomorph (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    ComplexVector n ≃ₜ ComplexVector n :=
  (Homeomorph.smulOfNeZero a ha).trans (Homeomorph.addLeft z₀)

theorem rescaleHomeomorph_apply (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0)
    (z : ComplexVector n) : rescaleHomeomorph z₀ a ha z = z₀ + a • z := rfl

theorem rescaleHomeomorph_inverse_apply (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0)
    (z : ComplexVector n) : (rescaleHomeomorph z₀ a ha).symm z = a⁻¹ • (z - z₀) := by
  change a⁻¹ • (-z₀ + z) = a⁻¹ • (z - z₀)
  congr 1
  abel

theorem rescaleHomeomorph_contDiff (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    ContDiff ℂ ∞ (rescaleHomeomorph z₀ a ha) := by
  change ContDiff ℂ ∞ (fun z : ComplexVector n => z₀ + a • z)
  fun_prop

theorem rescaleHomeomorph_inverse_contDiff (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    ContDiff ℂ ∞ (rescaleHomeomorph z₀ a ha).symm := by
  have heq : (rescaleHomeomorph z₀ a ha).symm = (fun z => a⁻¹ • (z - z₀)) :=
    funext (rescaleHomeomorph_inverse_apply z₀ a ha)
  rw [heq]
  fun_prop

def rescaledChart {M : ComplexManifold n}
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    OpenPartialHomeomorph (ComplexVector n) M.Carrier :=
  (rescaleHomeomorph z₀ a ha).toOpenPartialHomeomorph.trans e

theorem rescaledChart_apply {M : ComplexManifold n}
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) (z : ComplexVector n) :
    rescaledChart e z₀ a ha z = e (z₀ + a • z) := rfl

theorem rescaledChart_center {M : ComplexManifold n}
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    rescaledChart e z₀ a ha 0 = e z₀ := by simp only [rescaledChart_apply, smul_zero, add_zero]

end Yau.NodeProofs.F01Aux
