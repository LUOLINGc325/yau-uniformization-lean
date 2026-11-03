import Mathlib

/-! The real differential commuting with i is the same continuous complex differential. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem complex_smul_real_parts (c : ℂ) (v : E) :
    c • v = c.re • v + c.im • (Complex.I • v) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul]
  exact congrArg₂ (fun a b : E => a + b) (IsScalarTower.algebraMap_smul ℂ c.re v)
    (IsScalarTower.algebraMap_smul ℂ c.im (Complex.I • v))

def complexifyRealMap (L : E →L[ℝ] F) (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) : E →L[ℂ] F where
  toFun := L
  map_add' := L.map_add
  map_smul' := by
    intro c v
    calc
      L (c • v) = L (c.re • v + c.im • (Complex.I • v)) := congrArg L (complex_smul_real_parts c v)
      _ = c.re • L v + c.im • (Complex.I • L v) := by rw [map_add, map_smul, map_smul, hI]
      _ = c • L v := (complex_smul_real_parts c (L v)).symm
  cont := L.continuous

@[simp] theorem complexifyRealMap_apply (L : E →L[ℝ] F)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) (v : E) : complexifyRealMap L hI v = L v := rfl

@[simp] theorem complexifyRealMap_restrictScalars (L : E →L[ℝ] F)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    (complexifyRealMap L hI).restrictScalars ℝ = L := rfl

theorem hasFDerivAt_complex_of_real_and_I (f : E → F) (x : E)
    (hf : DifferentiableAt ℝ f x)
    (hI : ∀ v, fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v) :
    HasFDerivAt f (complexifyRealMap (fderiv ℝ f x) hI) x :=
  hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt rfl

theorem differentiableAt_complex_of_real_and_I (f : E → F) (x : E)
    (hf : DifferentiableAt ℝ f x)
    (hI : ∀ v, fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v) :
    DifferentiableAt ℂ f x := (hasFDerivAt_complex_of_real_and_I f x hf hI).differentiableAt

end Yau.Proofs.C04ChartsAux
