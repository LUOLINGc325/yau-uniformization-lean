import Yau.Proofs.F03ResolventPositivity
import Yau.Proofs.F03ExhaustionStepL2

/-! Actual supported and ambient resolvents preserve the real L2 order. -/
noncomputable section
open MeasureTheory Filter
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem l2_le_of_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f k : Lp ℝ 2 μ) (h : ∀ᵐ x ∂μ, f x ≤ k x) : f ≤ k := by
  apply sub_nonneg.mp
  apply (Lp.coeFn_nonneg (k-f)).mp
  filter_upwards [h,Lp.coeFn_sub k f] with x hx hs
  rw [hs,Pi.sub_apply]
  exact sub_nonneg.mpr hx

theorem dirichletAmbientStep_monotone (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {h : ℝ} (hh : 0 < h) :
    Monotone (dirichletAmbientStep g μ hμ Ω hΩ h hh) := by
  change Monotone (fun f => l2ZeroExtension μ Ω hΩ
    (dirichletStepResolvent g μ hμ Ω h hh (l2Restriction μ Ω f)))
  exact (l2ZeroExtension_monotone μ Ω hΩ).comp
    ((dirichletStepResolvent_monotone g μ hμ Ω hΩ hh).comp (l2Restriction_monotone μ Ω))

end Yau.Proofs.F03Aux
