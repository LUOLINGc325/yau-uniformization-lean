import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-! Integrating the two one-unit-shifted scalar comparisons costs only a fixed constant. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem shifted_primitive_upper {u v f g : ℝ → ℝ} {A k : ℝ}
    (hu : ∀ t, A ≤ t → HasDerivAt u (f t) t)
    (hv : ∀ t, A ≤ t → HasDerivAt v (g t) t)
    (hfg : ∀ t, A ≤ t → f t ≤ k * g (t + 1))
    {t : ℝ} (ht : A ≤ t) :
    u t ≤ k * v (t + 1) + (u A - k * v (A + 1)) := by
  have hanti : AntitoneOn (fun t => u t - k * v (t + 1)) (Ici A) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici A)
    · intro t ht
      change A ≤ t at ht
      have hshift := HasDerivAt.comp_add_const t 1 (hv (t + 1) (by linarith))
      convert! ((hu t ht).sub (hshift.const_mul k)).continuousAt.continuousWithinAt using 1
    · intro t ht
      have htA : A ≤ t := interior_subset ht
      have hshift := HasDerivAt.comp_add_const t 1 (hv (t + 1) (by linarith))
      have hh := (hu t htA).sub (hshift.const_mul k)
      convert! hh.hasDerivWithinAt using 1 <;>
        simp only [Function.comp_def, id_eq, mul_one]
    · intro t ht
      exact sub_nonpos.mpr (hfg t (interior_subset ht))
  have hh := hanti (le_refl A) ht ht
  linarith

theorem primitive_unit_shift_bound {s r : ℝ → ℝ} {A B : ℝ}
    (hs : ∀ t, A ≤ t → HasDerivAt s (r t) t)
    (hb : ∀ t, A ≤ t → r t ≤ B) {t : ℝ} (ht : A ≤ t) :
    s (t + 1) ≤ s t + B := by
  have hcont : ContinuousOn s (Ici A) := fun t ht => (hs t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ s (interior (Ici A)) :=
    fun t ht => (hs t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hder : ∀ t ∈ interior (Ici A), deriv s t ≤ B := by
    intro t ht
    rw [(hs t (interior_subset ht)).deriv]
    exact hb t (interior_subset ht)
  have hh := (convex_Ici A).image_sub_le_mul_sub_of_deriv_le hcont hdiff hder
    t ht (t + 1) (show A ≤ t + 1 by linarith) (by linarith)
  linarith

/-- The two primitive inequalities and a bounded unit time shift are
enough; no integrability of the Harnack error in time is assumed. -/
theorem ratio_bound_of_shifted_comparisons {u s : ℝ → ℝ} {t ε C B : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hB : 0 ≤ B) (hs : 0 < s t) (hu : 0 ≤ u t)
    (hupper : u t ≤ (1 + ε) * s (t + 1) + C)
    (hlower : s (t - 1) ≤ (1 + ε) * u t + C)
    (hshiftup : s (t + 1) ≤ s t + B)
    (hshiftdown : s t ≤ s (t - 1) + B) :
    |u t / s t - 1| ≤ ε + ((1 + ε) * B + C) / s t := by
  have hcup : 0 ≤ (1 + ε) * B + C := by positivity
  have hup : u t - s t ≤ ε * s t + ((1 + ε) * B + C) := by nlinarith
  have hlo : s t - u t ≤ ε * s t + ((1 + ε) * B + C) := by
    by_cases hle : u t ≤ s t
    · have hmul := mul_le_mul_of_nonneg_left hle hε
      nlinarith
    · have hneg : s t - u t ≤ 0 := by linarith
      exact hneg.trans (by positivity)
  have hrat : u t / s t - 1 = (u t - s t) / s t := by field_simp
  rw [hrat]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hs).mpr
    have hid : (-(ε + ((1 + ε) * B + C) / s t)) * s t =
        -(ε * s t + ((1 + ε) * B + C)) := by field_simp
    rw [hid]
    linarith
  · apply (div_le_iff₀ hs).mpr
    have hid : (ε + ((1 + ε) * B + C) / s t) * s t =
        ε * s t + ((1 + ε) * B + C) := by field_simp
    rwa [hid]

end Yau.Proofs.C04Aux
