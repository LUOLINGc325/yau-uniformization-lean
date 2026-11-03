import Yau.Proofs.F03FiniteDomainDomination
import Yau.Proofs.F03DirichletClassicalPairing

/-! Genuine finite-domain heat order at every interior point. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem dirichletClassicalHeat_mono_domain (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω Γ : Set M.Carrier) (hΩ : IsOpen Ω) (hΓ : IsOpen Γ) (hΩΓ : Ω ⊆ Γ)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ (l2Restriction μ Ω f) x t ≤
      dirichletClassicalHeat g hK μ hμ Γ hΓ (l2Restriction μ Γ f) x t := by
  let a := l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t (l2Restriction μ Ω f))
  let b := l2ZeroExtension μ Γ hΓ.measurableSet (dirichletHeat g μ hμ Γ t (l2Restriction μ Γ f))
  have horder := dirichletHeat_mono_domain g hK μ hμ Ω Γ hΩ hΓ hΩΓ t ht f hf
  have hAE := (Lp.coeFn_nonneg (b-a)).mpr (sub_nonneg.mpr horder)
  apply leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ _ ht)
    ((dirichletClassicalHeat_continuousOn g hK μ hμ Γ hΓ _ ht).mono hΩΓ)
  filter_upwards [ae_restrict_of_ae hAE,ae_restrict_of_ae (Lp.coeFn_sub b a),
    ae_restrict_of_ae (dirichletClassicalHeat_ambient_ae g hK μ hμ Ω hΩ (l2Restriction μ Ω f) ht),
    ae_restrict_of_ae (dirichletClassicalHeat_ambient_ae g hK μ hμ Γ hΓ (l2Restriction μ Γ f) ht)]
    with x hx hs hΩx hΓx
  rw [hs,Pi.sub_apply] at hx
  exact hΩx.trans_le ((sub_nonneg.mp hx).trans_eq hΓx.symm)

end Yau.Proofs.F03Aux
