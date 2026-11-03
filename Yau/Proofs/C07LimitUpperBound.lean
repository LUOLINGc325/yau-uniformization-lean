import Yau.Proofs.D04AtlasGlueError

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

/-- Clipping a candidate limit at an upper bound already obeyed by the
sequence decreases the actual extended-real L¹ error. -/
theorem erealDist_min_upper {a b : EReal} {C : ℝ} (ha : a ≤ (C : EReal)) :
    erealDist a (min b (C : EReal)) ≤ erealDist a b := by
  by_cases hb : b ≤ (C : EReal)
  · rw [min_eq_left hb]
  have hCb : (C : EReal) < b := lt_of_not_ge hb
  rw [min_eq_right hCb.le]
  cases a with
  | bot => cases b <;> simp_all [erealDist]
  | top => exact False.elim (by simpa using ha)
  | coe a =>
    cases b with
    | bot => exact False.elim (by simpa using hCb)
    | top => simp [erealDist]
    | coe b =>
      have haC : a ≤ C := EReal.coe_le_coe_iff.mp ha
      have hCb' : C < b := EReal.coe_lt_coe_iff.mp hCb
      have hab : a ≠ b := ne_of_lt (haC.trans_lt hCb')
      by_cases haeq : a = C
      · subst a; simp [erealDist]
      · simp only [erealDist, EReal.coe_eq_coe_iff, haeq, hab, ite_false,
          EReal.coe_ne_bot, EReal.coe_ne_top, false_or, EReal.toReal_coe]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_nonpos (sub_nonpos.mpr haC), abs_of_nonpos (sub_nonpos.mpr (haC.trans hCb'.le))]
        linarith

/-- A local L¹ limit inherits every eventual finite upper bound almost
everywhere.  The proof uses actual `erealDist` convergence and uniqueness,
without choosing pointwise representatives of the original sequence. -/
theorem limit_ae_le_of_eventually_bounded {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {us : ℕ → A → EReal} {u : A → EReal} {C : ℝ}
    (hus : ∀ᶠ j in atTop, AEMeasurable (us j) μ)
    (hu : AEMeasurable u μ)
    (hconv : Tendsto (fun j => ∫⁻ x, erealDist (us j x) (u x) ∂μ) atTop (𝓝 0))
    (hupper : ∀ᶠ j in atTop, ∀ᵐ x ∂μ, us j x ≤ (C : EReal)) :
    ∀ᵐ x ∂μ, u x ≤ (C : EReal) := by
  have hle : ∀ᶠ j in atTop,
      (∫⁻ x, erealDist (us j x) (min (u x) (C : EReal)) ∂μ) ≤
      ∫⁻ x, erealDist (us j x) (u x) ∂μ := by
    filter_upwards [hupper] with j hj
    exact lintegral_mono_ae (hj.mono (fun x hx => erealDist_min_upper hx))
  have hconv' : Tendsto (fun j => ∫⁻ x, erealDist (us j x) (min (u x) (C : EReal)) ∂μ)
      atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
      (Filter.Eventually.of_forall (fun _ => bot_le)) hle
  have heq := Yau.Proofs.D04AtlasGlueAux.limits_unique_of_erealDist hus hu
    (hu.min aemeasurable_const) hconv hconv'
  exact heq.mono (fun x hx => hx.symm ▸ min_le_right (u x) (C : EReal))

end Yau.Proofs.C07Aux
