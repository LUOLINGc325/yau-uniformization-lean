import Yau.Proofs.V03ExteriorTwoForm
import Yau.Proofs.V03LeviChain

/-! Native real bilinearity and complex-structure identities for an
actual invariant alternating two-form. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem twoForm_real_smul_left (Ω : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    Ω ![c • u, v] = c * Ω ![u, v] := by
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap, smul_eq_mul] using
    Ω.toAlternatingMap.map_vecCons_smul ![v] c u

theorem twoForm_neg_left (Ω : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) : Ω ![-u, v] = -Ω ![u, v] := by
  simpa only [neg_one_smul, neg_one_mul] using twoForm_real_smul_left Ω (-1) u v

theorem twoForm_neg_right (Ω : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) : Ω ![u, -v] = -Ω ![u, v] := by
  rw [twoForm_swap, twoForm_neg_left, neg_neg, twoForm_swap]

theorem twoForm_Jcross (Ω : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v : E, Ω ![Complex.I • u, Complex.I • v] = Ω ![u, v]) (u v : E) :
    Ω ![Complex.I • u, v] = -Ω ![u, Complex.I • v] := by
  have hh := hJ u (Complex.I • v)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, twoForm_neg_right] at hh
  linarith

theorem twoFormCoefficient_contDiffOn {U : Set E} {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ}
    (hΩ : ContDiffOn ℝ ∞ Ω U) (u v : E) : ContDiffOn ℝ ∞ (fun p => Ω p ![u, v]) U := by
  have hh := (ContinuousAlternatingMap.apply ℝ E ℝ ![u, v]).contDiff.comp_contDiffOn hΩ
  simpa only [Function.comp_def, ContinuousAlternatingMap.apply_apply] using hh

end Yau.Blueprint.V03Proof
