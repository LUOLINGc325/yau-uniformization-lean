import Yau.Proofs.F03DirichletCoreGreen
import Yau.LeafProofs.L19HeatInitial

/-! The actual computed compact Laplacian is the supported heat generator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletResolvent_compact_generator (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (k : dirichletCore g μ hμ O) :
    dirichletResolvent g μ hμ O
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val) -
        l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val))) =
      l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val) := by
  rw [← map_sub,← scalarEnergyGreenTest_L2]
  exact dirichletResolvent_greenTest g hK μ hμ O hO k

theorem dirichletComplexHeat_right_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    dirichletComplexHeatInverse g μ hμ O t * dirichletComplexResolvent g μ hμ O =
      dirichletComplexHeat g μ hμ O t := by
  rw [dirichletComplexHeat_factor g μ hμ O ht]
  exact ((Commute.refl (dirichletComplexResolvent g μ hμ O)).cfc_real
    (scalarHeatInverseMultiplier t)).eq

theorem dirichletHeat_right_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t) :
    dirichletHeatInverse g μ hμ O t * dirichletResolvent g μ hμ O =
      dirichletHeat g μ hμ O t := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Function.LeftInverse.injective (heatLpRe_ofReal (μ.restrict O)))
  rw [mul_apply_eq_comp,dirichletHeatInverse_ofReal g μ hμ O ht,
    ← dirichletComplexResolvent_ofReal,dirichletHeat_ofReal,
    ← mul_apply_eq_comp,dirichletComplexHeat_right_factor g μ hμ O ht]

theorem dirichletHeat_compact_hasDerivAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (k : dirichletCore g μ hμ O)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => dirichletHeat g μ hμ O s
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)))
      (dirichletHeat g μ hμ O t (l2Restriction μ O
        (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)))) t := by
  have hd := dirichletHeat_apply_hasDerivAt g μ hμ O ht
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val))
  have hR := dirichletResolvent_compact_generator g hK μ hμ O hO k
  have hIR : dirichletHeatInverse g μ hμ O t
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) =
      dirichletHeat g μ hμ O t
        (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val) -
          l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val))) := by
    conv_lhs => rw [← hR]
    exact congrArg (fun A : Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 (μ.restrict O) => A _)
      (dirichletHeat_right_factor g μ hμ O ht)
  rw [hIR,map_sub] at hd
  convert hd using 1 <;> abel

end Yau.Proofs.F03Aux
