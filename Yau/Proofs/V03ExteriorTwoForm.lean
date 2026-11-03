import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-! Native exterior differentiation of genuine real two-forms and
pullback closure, with the actual alternating signs and normalization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem twoForm_swap (Ω : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) : Ω ![u, v] = -Ω ![v, u] := by
  have hs := Ω.toAlternatingMap.map_swap (v := ![v, u]) (i := (0 : Fin 2)) (j := (1 : Fin 2))
    (by decide : (0 : Fin 2) ≠ 1)
  have he : (![v, u] : Fin 2 → E) ∘ Equiv.swap 0 1 = ![u, v] := by
    funext i
    fin_cases i <;> simp
  simpa only [he, ContinuousAlternatingMap.coe_toAlternatingMap] using hs

theorem extDeriv_twoForm_apply {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x : E}
    (hΩ : DifferentiableAt ℝ Ω x) (u v w : E) :
    extDeriv Ω x ![u, v, w] = fderiv ℝ (fun p => Ω p ![v, w]) x u -
      fderiv ℝ (fun p => Ω p ![u, w]) x v + fderiv ℝ (fun p => Ω p ![u, v]) x w := by
  have h0 : (0 : Fin 3).removeNth (![u, v, w] : Fin 3 → E) = ![v, w] := by
    funext i
    fin_cases i <;> rfl
  have h1 : (1 : Fin 3).removeNth (![u, v, w] : Fin 3 → E) = ![u, w] := by
    funext i
    fin_cases i <;> rfl
  have h2 : (2 : Fin 3).removeNth (![u, v, w] : Fin 3 → E) = ![u, v] := by
    funext i
    fin_cases i <;> rfl
  rw [extDeriv_apply hΩ]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val •
    fderiv ℝ (fun p => Ω p (i.removeNth ![u, v, w])) x (![u, v, w] i)) = _
  rw [Fin.sum_univ_three]
  simp only [h0, h1, h2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    neg_one_sq, one_zsmul, neg_one_zsmul, sub_eq_add_neg]
  rfl

theorem closedTwoForm_pullback {Ω : F → F [⋀^Fin 2]→L[ℝ] ℝ} {T : E → F} {z : E}
    (hΩ : DifferentiableAt ℝ Ω (T z)) (hT : ContDiffAt ℝ 2 T z)
    (hclosed : extDeriv Ω (T z) = 0) :
    extDeriv (fun x => (Ω (T x)).compContinuousLinearMap (fderiv ℝ T x)) z = 0 := by
  rw [extDeriv_pullback hΩ hT (by simp), hclosed]
  rfl

end Yau.Blueprint.V03Proof
