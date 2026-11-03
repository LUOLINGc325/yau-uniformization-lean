import Yau.Proofs.V03ScalarLeviTwoForm
import Yau.Proofs.V03WirtingerDirections
import Yau.Proofs.V03JTwoFormPolarization

/-! The native scalar Levi two-form is exactly determined by the
original real diagonal mixed calculator, also under complex linear pullback. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem twoForm_pullback_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : F [⋀^Fin 2]→L[ℝ] ℝ) (A : E →L[ℝ] F) (u v : E) :
    Ω.compContinuousLinearMap A ![u, v] = Ω ![A u, A v] := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have he : (A : E → F) ∘ ![u, v] = ![A u, A v] := by funext i; fin_cases i <;> rfl
  rw [he]

theorem twoForm_complex_pullback_J {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Ω : F [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v : F, Ω ![Complex.I • u, Complex.I • v] = Ω ![u, v])
    (A : E →L[ℂ] F) (u v : E) :
    Ω.compContinuousLinearMap (A.restrictScalars ℝ) ![Complex.I • u, Complex.I • v] =
      Ω.compContinuousLinearMap (A.restrictScalars ℝ) ![u, v] := by
  rw [twoForm_pullback_apply, twoForm_pullback_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  exact hJ _ _

theorem scalarLeviTwoForm_diagonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v : E) :
    scalarLeviTwoForm f z ![v, Complex.I • v] =
      2 * (wirt (fun u => wirtBar (fun u' => (f u' : ℂ)) u v) z v).re := by
  rw [scalarLeviTwoForm_apply hf, leviTwoForm, wirt_smul_direction]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]

theorem scalarLeviTwoForm_eq_of_real_diagonal {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → ℝ} {g : F → ℝ} {z : E} {w : F}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g w) (A : E →L[ℂ] F)
    (heq : ∀ v : E,
      (wirt (fun u => wirtBar (fun u' => (f u' : ℂ)) u v) z v).re =
      (wirt (fun u => wirtBar (fun u' => (g u' : ℂ)) u (A v)) w (A v)).re) :
    scalarLeviTwoForm f z = (scalarLeviTwoForm g w).compContinuousLinearMap (A.restrictScalars ℝ) := by
  apply JTwoForm_ext_diagonal (scalarLeviTwoForm_J hf)
    (twoForm_complex_pullback_J _ (scalarLeviTwoForm_J hg) A)
  intro v
  rw [scalarLeviTwoForm_diagonal hf, twoForm_pullback_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  rw [scalarLeviTwoForm_diagonal hg, heq v]

end Yau.Blueprint.V03Proof
