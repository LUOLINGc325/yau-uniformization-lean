import Yau.Proofs.V03LeviChain
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The full actual mixed derivative of a Hilbert norm square. This
identity retains the trace's genuine mixed derivative rather than imposing
any parameter-acceleration bound. -/

open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem secondFDeriv_norm_sq (x v w : H) :
    fderiv ℝ (fderiv ℝ (fun y : H => ‖y‖ ^ 2)) x v w = 2 * ⟪v, w⟫ := by
  rw [fderiv_norm_sq]
  simp only [two_smul]
  rw [fderiv_add (innerSL ℝ (E := H)).differentiableAt
    (innerSL ℝ (E := H)).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, add_apply]
  change ⟪v, w⟫ + ⟪v, w⟫ = 2 * ⟪v, w⟫
  ring

theorem secondFDeriv_norm_sq_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → H} {z : E} (hU : ContDiffAt ℝ 2 U z) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => ‖U y‖ ^ 2)) z v w =
      2 * (⟪fderiv ℝ U z v, fderiv ℝ U z w⟫ +
        ⟪U z, fderiv ℝ (fderiv ℝ U) z v w⟫) := by
  have hq : ContDiffAt ℝ 2 (fun x : H => ‖x‖ ^ 2) (U z) :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hh := secondFDeriv_comp hU hq v w
  simp only [Function.comp_def, secondFDeriv_norm_sq, fderiv_norm_sq_apply,
    two_smul, ContinuousLinearMap.add_apply] at hh
  change _ = 2 * ⟪fderiv ℝ U z v, fderiv ℝ U z w⟫ +
    (⟪U z, fderiv ℝ (fderiv ℝ U) z v w⟫ + ⟪U z, fderiv ℝ (fderiv ℝ U) z v w⟫) at hh
  linarith

theorem mixedReal_norm_sq {U : ℂ → H} (hU : ContDiffAt ℝ 2 U 0) :
    mixedReal (fun z => ‖U z‖ ^ 2) =
      (1 / 2 : ℝ) * (‖fderiv ℝ U 0 1‖ ^ 2 + ‖fderiv ℝ U 0 Complex.I‖ ^ 2) +
      (1 / 2 : ℝ) * ⟪U 0, fderiv ℝ (fderiv ℝ U) 0 1 1 +
        fderiv ℝ (fderiv ℝ U) 0 Complex.I Complex.I⟫ := by
  unfold mixedReal
  rw [mixedWirt_real_diagonal (hU.norm_sq ℝ)]
  simp only [secondFDeriv_norm_sq_comp hU, smul_eq_mul, mul_one,
    real_inner_self_eq_norm_sq, inner_add_right]
  ring

theorem abs_mixedReal_norm_sq_le {U : ℂ → H} (hU : ContDiffAt ℝ 2 U 0) :
    |mixedReal (fun z => ‖U z‖ ^ 2)| ≤
      (1 / 2 : ℝ) * (‖fderiv ℝ U 0 1‖ ^ 2 + ‖fderiv ℝ U 0 Complex.I‖ ^ 2) +
      (1 / 2 : ℝ) * ‖U 0‖ * ‖fderiv ℝ (fderiv ℝ U) 0 1 1 +
        fderiv ℝ (fderiv ℝ U) 0 Complex.I Complex.I‖ := by
  rw [mixedReal_norm_sq hU]
  have hnonneg : 0 ≤ (1 / 2 : ℝ) *
      (‖fderiv ℝ U 0 1‖ ^ 2 + ‖fderiv ℝ U 0 Complex.I‖ ^ 2) := by positivity
  have hh := abs_add_le ((1 / 2 : ℝ) *
      (‖fderiv ℝ U 0 1‖ ^ 2 + ‖fderiv ℝ U 0 Complex.I‖ ^ 2))
    ((1 / 2 : ℝ) * ⟪U 0, fderiv ℝ (fderiv ℝ U) 0 1 1 +
      fderiv ℝ (fderiv ℝ U) 0 Complex.I Complex.I⟫)
  rw [abs_of_nonneg hnonneg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hh
  have hb := abs_real_inner_le_norm (U 0) (fderiv ℝ (fderiv ℝ U) 0 1 1 +
    fderiv ℝ (fderiv ℝ U) 0 Complex.I Complex.I)
  nlinarith

end Yau.Blueprint.V03Proof
