import Yau.Proofs.V03JTwoFormAlgebra

/-! A genuine complex-invariant real two-form is determined by its
complex diagonal, with an explicit native polarization identity. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem twoForm_add_left (Ω : E [⋀^Fin 2]→L[ℝ] ℝ) (u v w : E) :
    Ω ![u + v, w] = Ω ![u, w] + Ω ![v, w] := by
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap] using
    Ω.toAlternatingMap.map_vecCons_add ![w] u v

theorem twoForm_add_right (Ω : E [⋀^Fin 2]→L[ℝ] ℝ) (u v w : E) :
    Ω ![u, v + w] = Ω ![u, v] + Ω ![u, w] := by
  calc
    _ = -Ω ![v + w, u] := twoForm_swap Ω _ _
    _ = _ := by rw [twoForm_add_left, twoForm_swap Ω v u, twoForm_swap Ω w u]; ring

theorem JTwoForm_polarization (Ω : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hJ : ∀ u v : E, Ω ![Complex.I • u, Complex.I • v] = Ω ![u, v]) (u v : E) :
    2 * Ω ![u, v] = Ω ![u, Complex.I • u] + Ω ![v, Complex.I • v] -
      Ω ![u + Complex.I • v, Complex.I • (u + Complex.I • v)] := by
  rw [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, twoForm_add_left,
    twoForm_add_right, twoForm_add_right, twoForm_neg_right, twoForm_neg_right,
    hJ v u, twoForm_swap Ω v u, twoForm_swap Ω (Complex.I • v) v]
  ring

theorem JTwoForm_ext_diagonal {Ω₁ Ω₂ : E [⋀^Fin 2]→L[ℝ] ℝ}
    (hJ₁ : ∀ u v : E, Ω₁ ![Complex.I • u, Complex.I • v] = Ω₁ ![u, v])
    (hJ₂ : ∀ u v : E, Ω₂ ![Complex.I • u, Complex.I • v] = Ω₂ ![u, v])
    (hdiag : ∀ u : E, Ω₁ ![u, Complex.I • u] = Ω₂ ![u, Complex.I • u]) : Ω₁ = Ω₂ := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]
  have h₁ := JTwoForm_polarization Ω₁ hJ₁ (v 0) (v 1)
  have h₂ := JTwoForm_polarization Ω₂ hJ₂ (v 0) (v 1)
  rw [hdiag (v 0), hdiag (v 1), hdiag (v 0 + Complex.I • v 1)] at h₁
  linarith

end Yau.Blueprint.V03Proof
