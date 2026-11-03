import Yau.Proofs.F03L2RestrictionPairing
import Yau.Proofs.F03DirichletResolvent

/-! Genuine supported resolvent Green identity for the actual compact core. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem dirichletL2_adjoint_greenTest (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (k : dirichletCore g μ hμ O) :
    (dirichletL2 g μ hμ O).adjoint
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k.val))) =
      dirichletCoreToEnergy g μ hμ O k := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,real_inner_comm
    (dirichletL2 g μ hμ O v)
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k.val))),
    ← l2ZeroExtension_inner_left μ O hO,
    dirichletL2_zeroExtension g μ hμ O hO v,
    ← scalarEnergyL2_green g hK μ hμ v.val k.val]
  change inner ℝ v.val (k.val : ScalarEnergySpace g μ hμ) =
    inner ℝ (k.val : ScalarEnergySpace g μ hμ) v.val
  exact real_inner_comm _ _

theorem dirichletResolvent_greenTest (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (k : dirichletCore g μ hμ O) :
    dirichletResolvent g μ hμ O
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k.val))) =
      l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val) := by
  change dirichletL2 g μ hμ O ((dirichletL2 g μ hμ O).adjoint _) = _
  rw [dirichletL2_adjoint_greenTest g hK μ hμ O hO k,dirichletL2_core]

end Yau.Proofs.F03Aux
