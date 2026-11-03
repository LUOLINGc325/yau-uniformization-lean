import Yau.LeafProofs.L19ScalarMarkov

/-! Signed bounded-function estimates for the actual scalar resolvent. -/

noncomputable section
open MeasureTheory Filter
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem lp_posPart_sub_negPart {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : Lp ℝ 2 μ) : f = Lp.posPart f - Lp.negPart f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_negPart f,
    Lp.coeFn_sub (Lp.posPart f) (Lp.negPart f)] with x hp hn hs
  rw [hs, Pi.sub_apply, hp, hn]
  rcases le_total (f x) 0 with hf | hf
  · rw [max_eq_right hf, min_eq_left hf]
    ring
  · rw [max_eq_left hf, min_eq_right hf]
    ring

theorem lp_posPart_negPart_bounded {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : Lp ℝ 2 μ) {K : ℝ}
    (hf : ∀ᵐ x ∂μ, |f x| ≤ K) :
    (∀ᵐ x ∂μ, 0 ≤ Lp.posPart f x ∧ Lp.posPart f x ≤ K) ∧
      (∀ᵐ x ∂μ, 0 ≤ Lp.negPart f x ∧ Lp.negPart f x ≤ K) := by
  have hall : ∀ᵐ x ∂μ,
      (0 ≤ Lp.posPart f x ∧ Lp.posPart f x ≤ K) ∧
        (0 ≤ Lp.negPart f x ∧ Lp.negPart f x ≤ K) := by
    filter_upwards [hf, Lp.coeFn_posPart f, Lp.coeFn_negPart f] with x hx hp hn
    rw [hp, hn]
    have hb := abs_le.mp hx
    have hK : 0 ≤ K := (abs_nonneg _).trans hx
    exact ⟨⟨le_max_right _ _, max_le hb.2 hK⟩,
      ⟨neg_nonneg.mpr (min_le_right _ _), by
        rw [neg_le]
        exact le_min hb.1 (neg_nonpos.mpr hK)⟩⟩
  exact ⟨hall.mono (fun _ h => h.1), hall.mono (fun _ h => h.2)⟩

/-- The actual resolvent is an L∞ contraction on its L² bounded inputs.
No global constant function is inserted into L². -/
theorem scalarResolvent_abs_markov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h)
    (K : ℝ) (hK : 0 < K) (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, |f x| ≤ K) :
    ∀ᵐ x ∂μ, |scalarResolvent g μ hμ h hh f x| ≤ K := by
  have hparts := lp_posPart_negPart_bounded f hf
  have hp := scalarResolvent_markov g μ hμ h hh K hK (Lp.posPart f) hparts.1
  have hn := scalarResolvent_markov g μ hμ h hh K hK (Lp.negPart f) hparts.2
  have heq : scalarResolvent g μ hμ h hh f =
      scalarResolvent g μ hμ h hh (Lp.posPart f) - scalarResolvent g μ hμ h hh (Lp.negPart f) := by
    have hh := congrArg (scalarResolvent g μ hμ h hh) (lp_posPart_sub_negPart f)
    rwa [map_sub] at hh
  filter_upwards [hp, hn, Lp.coeFn_sub (scalarResolvent g μ hμ h hh (Lp.posPart f))
    (scalarResolvent g μ hμ h hh (Lp.negPart f))] with x hpx hnx hsub
  rw [heq, hsub, Pi.sub_apply]
  exact abs_le.mpr ⟨by linarith only [hpx.1, hnx.2], by linarith only [hpx.2, hnx.1]⟩

end Yau.LeafProofs.L19Aux
