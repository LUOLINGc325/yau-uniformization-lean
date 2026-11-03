import Yau.Proofs.V03BilinearTwoForm
import Yau.Proofs.V03LeviTwoForm
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! The actual scalar i∂∂bar calculator is a genuine continuous real
alternating two-form, smoothly in its point, with its original normalization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def complexStructureRealL : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

theorem complexStructureRealL_apply (u : E) : complexStructureRealL u = Complex.I • u := rfl

def scalarLeviBilinear (f : E → ℝ) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ (fderiv ℝ f) z).flip.comp complexStructureRealL

theorem scalarLeviBilinear_apply (f : E → ℝ) (z u v : E) :
    scalarLeviBilinear f z u v = fderiv ℝ (fderiv ℝ f) z v (Complex.I • u) := rfl

def scalarLeviTwoForm (f : E → ℝ) (z : E) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  bilinearTwoForm (scalarLeviBilinear f z)

theorem scalarLeviTwoForm_apply {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u v : E) :
    scalarLeviTwoForm f z ![u, v] = leviTwoForm f z u v := by
  rw [scalarLeviTwoForm, bilinearTwoForm_apply, scalarLeviBilinear_apply, scalarLeviBilinear_apply,
    leviTwoForm_eq_secondFDeriv hf]
  rw [hf.isSymmSndFDerivAt (by norm_num) u (Complex.I • v)]

theorem scalarLeviTwoForm_J {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u v : E) :
    scalarLeviTwoForm f z ![Complex.I • u, Complex.I • v] = scalarLeviTwoForm f z ![u, v] := by
  rw [scalarLeviTwoForm_apply hf, scalarLeviTwoForm_apply hf,
    leviTwoForm_eq_secondFDeriv hf, leviTwoForm_eq_secondFDeriv hf]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, ContinuousLinearMap.neg_apply]
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  rw [hs (Complex.I • v) u, hs v (Complex.I • u)]
  ring

theorem scalarLeviBilinear_contDiffOn [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (scalarLeviBilinear f) U := by
  have hH := (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).fderiv_of_isOpen hU (m := ∞) (by simp)
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [scalarLeviBilinear_apply]
  exact (hH.clm_apply contDiffOn_const).clm_apply contDiffOn_const

theorem scalarLeviTwoForm_contDiffOn [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (scalarLeviTwoForm f) U :=
  bilinearTwoForm_contDiffOn (scalarLeviBilinear_contDiffOn hU hf)

end Yau.Blueprint.V03Proof
