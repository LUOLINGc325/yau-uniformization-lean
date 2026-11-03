import Yau.Proofs.F03DirichletClassicalDerivative
import Yau.Proofs.F03DirichletCoreGenerator

/-! The actual pointwise compact-source generator commutes with classical supported heat. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletClassicalHeat_compact_laplacian
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (k : dirichletCore g μ hμ O)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) (hx : x ∈ O) :
    laplacian g.form (fun y => dirichletClassicalHeat g hK μ hμ O hO
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) y t) x =
      dirichletClassicalHeat g hK μ hμ O hO
        (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val))) x t := by
  let s := t/2
  have hs : 0 < s := half_pos ht
  have hst : s < t := half_lt_self ht
  have hG := (dirichletHeat_apply_hasDerivAt g μ hμ O (sub_pos.mpr hst)
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val))).unique
      (dirichletHeat_compact_hasDerivAt g hK μ hμ O hO.measurableSet k (sub_pos.mpr hst))
  change dirichletHeatDerivativeOperator g μ hμ O (t-s)
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) =
      dirichletHeat g μ hμ O (t-s)
        (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val))) at hG
  rw [dirichletClassicalHeat_laplacian_split g hK μ hμ O hO _ x hx hs hst,hG]
  have htime : s+(t-s)=t := by ring
  simpa only [htime] using (dirichletClassicalHeat_semigroup g hK μ hμ O hO
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)))
    hs (sub_pos.mpr hst).le x hx).symm

theorem dirichletClassicalHeat_compact_hasDerivAt
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (k : dirichletCore g μ hμ O)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) (hx : x ∈ O) :
    HasDerivAt (dirichletClassicalHeat g hK μ hμ O hO
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) x)
      (dirichletClassicalHeat g hK μ hμ O hO
        (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val))) x t) t := by
  rw [← dirichletClassicalHeat_compact_laplacian g hK μ hμ O hO k ht x hx]
  exact dirichletClassicalHeat_hasDerivAt g hK μ hμ O hO _ x hx ht

end Yau.Proofs.F03Aux
