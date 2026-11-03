import Yau.Proofs.V03BilinearTwoForm
import Yau.Proofs.V03ScalarLeviTwoForm
import Yau.Proofs.V03LeviNaturality

/-! Native pullback of genuine bilinear and scalar Levi two-forms. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pullbackBilinear (A : F →L[ℝ] F →L[ℝ] ℝ) (T : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ).flip T).comp (A.comp T)

theorem pullbackBilinear_apply (A : F →L[ℝ] F →L[ℝ] ℝ) (T : E →L[ℝ] F) (u v : E) :
    pullbackBilinear A T u v = A (T u) (T v) := rfl

theorem bilinearTwoForm_pullback (A : F →L[ℝ] F →L[ℝ] ℝ) (T : E →L[ℝ] F) :
    bilinearTwoForm (pullbackBilinear A T) = (bilinearTwoForm A).compContinuousLinearMap T := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, bilinearTwoForm_apply, pullbackBilinear_apply, pullbackBilinear_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hTv : (T : E → F) ∘ ![v 0, v 1] = ![T (v 0), T (v 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hTv]
  exact (bilinearTwoForm_apply A _ _).symm

theorem pullbackBilinear_contDiffOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ E] {U : Set P} {A : P → F →L[ℝ] F →L[ℝ] ℝ} {T : P → E →L[ℝ] F}
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (fun p => pullbackBilinear (A p) (T p)) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [pullbackBilinear_apply]
  exact (hA.clm_apply (hT.clm_apply contDiffOn_const)).clm_apply (hT.clm_apply contDiffOn_const)

theorem scalarLeviTwoForm_holomorphic_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : E → F} {f : F → ℝ} {z : E} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) :
    scalarLeviTwoForm (fun p => f (T p)) z =
      (scalarLeviTwoForm f (T z)).compContinuousLinearMap ((fderiv ℂ T z).restrictScalars ℝ) := by
  have hcomp : ContDiffAt ℝ 2 (fun p => f (T p)) z := hf.comp z (hT.restrict_scalars ℝ)
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, scalarLeviTwoForm_apply hcomp]
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hTv : (((fderiv ℂ T z).restrictScalars ℝ) : E → F) ∘ ![v 0, v 1] =
      ![fderiv ℂ T z (v 0), fderiv ℂ T z (v 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hTv]
  rw [scalarLeviTwoForm_apply hf]
  exact congrArg (fun w : ℂ => 2 * w.im) (mixedWirt_holomorphic_comp hT hf (v 0) (v 1))

end Yau.Blueprint.V03Proof
