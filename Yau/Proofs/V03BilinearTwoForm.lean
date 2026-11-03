import Yau.Proofs.V03ExteriorTwoForm

/-! A genuine continuous real bilinear form yields its normalized
alternating two-form, smoothly in the original bilinear coefficients. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def oneFormOfCLM : (E →L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap

theorem oneFormOfCLM_apply (A : E →L[ℝ] ℝ) (v : E) : oneFormOfCLM A ![v] = A v := rfl

def bilinearTwoForm (A : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin (oneFormOfCLM.comp A)

theorem bilinearTwoForm_apply (A : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    bilinearTwoForm A ![u, v] = (1 / 2 : ℝ) * (A u v - A v u) := by
  have h0 : (0 : Fin 2).removeNth (![u, v] : Fin 2 → E) = ![v] := by
    funext i
    fin_cases i
    rfl
  have h1 : (1 : Fin 2).removeNth (![u, v] : Fin 2 → E) = ![u] := by
    funext i
    fin_cases i
    rfl
  rw [bilinearTwoForm, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  change (1 / 2 : ℝ) * (∑ i : Fin 2, (-1 : ℤ) ^ i.val •
    (oneFormOfCLM.comp A) (![u, v] i) (i.removeNth ![u, v])) = _
  rw [Fin.sum_univ_two]
  simp only [h0, h1, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_zsmul, neg_one_zsmul, ContinuousLinearMap.comp_apply,
    oneFormOfCLM_apply, sub_eq_add_neg]

theorem bilinearTwoForm_contDiffOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {A : P → E →L[ℝ] E →L[ℝ] ℝ} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun p => bilinearTwoForm (A p)) U := by
  have hOne : ContDiffOn ℝ ∞ (fun p => oneFormOfCLM.comp (A p)) U :=
    contDiffOn_const.clm_comp hA
  have hAlt := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp_contDiffOn hOne
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).smul hAlt

end Yau.Blueprint.V03Proof
