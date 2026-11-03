import Yau.Proofs.F03DirichletHeatDomination
import Yau.Proofs.F03UnivHeatEquality
import Yau.Proofs.F03DirichletClassicalPairing

/-! Actual-volume order gives pointwise domain-to-whole heat comparison. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletClassicalHeat_le_univ (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ≤
      dirichletClassicalHeat g hK μ hμ Set.univ isOpen_univ
        (l2Restriction μ Set.univ (l2ZeroExtension μ Ω hΩ.measurableSet f)) x t := by
  let F := l2ZeroExtension μ Ω hΩ.measurableSet f
  let fU := l2Restriction μ Set.univ F
  have hF : 0 ≤ F := l2ZeroExtension_nonneg μ Ω hΩ.measurableSet f ((Lp.coeFn_nonneg _).mp hf)
  have hD := dirichletHeat_le_ambient g hK μ hμ Ω hΩ t ht F hF
  rw [l2Restriction_zeroExtension,← dirichletHeat_univ g μ hμ t ht F] at hD
  let a := l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f)
  let b := l2ZeroExtension μ Set.univ MeasurableSet.univ (dirichletHeat g μ hμ Set.univ t fU)
  have hAE : ∀ᵐ x ∂μ, a x ≤ b x := by
    have hnonneg := (Lp.coeFn_nonneg (b-a)).mpr (sub_nonneg.mpr hD)
    filter_upwards [hnonneg,Lp.coeFn_sub b a] with x hx hs
    rw [hs,Pi.sub_apply] at hx
    exact sub_nonneg.mp hx
  apply leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f ht)
    ((dirichletClassicalHeat_continuousOn g hK μ hμ Set.univ isOpen_univ fU ht).mono (subset_univ Ω))
  filter_upwards [ae_restrict_of_ae hAE,
    ae_restrict_of_ae (dirichletClassicalHeat_ambient_ae g hK μ hμ Ω hΩ f ht),
    ae_restrict_of_ae (dirichletClassicalHeat_ambient_ae g hK μ hμ Set.univ isOpen_univ fU ht)]
    with x hx hΩx hUx
  exact hΩx.trans_le (hx.trans_eq hUx.symm)

end Yau.Proofs.F03Aux
