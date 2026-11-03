import Yau.Proofs.F04AmbientEnergy
import Yau.Proofs.F03DirichletEnergyIdentity
import Yau.LeafProofs.L19ScalarResolvent

/-! The original ambient coercive form uses the actual whole-manifold differential. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau F04Proof LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletL2_univ_inner (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (u v : ScalarEnergySpace g μ hμ) :
    inner ℝ (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ u))
      (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ v))=
      inner ℝ (scalarEnergyL2 g μ hμ u) (scalarEnergyL2 g μ hμ v) := by
  rw [L2.inner_def,L2.inner_def]
  let F : M.Carrier → ℝ := fun x => inner ℝ
    (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ u) x)
    (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ v) x)
  have hmeasure : (∫ x, F x ∂μ.restrict Set.univ)=(∫ x, F x ∂μ) :=
    congrArg (fun ν : Measure M.Carrier => ∫ x, F x ∂ν)
      (show μ.restrict Set.univ=μ from Measure.restrict_univ)
  change (∫ x, F x ∂μ.restrict Set.univ)=_
  rw [hmeasure]
  dsimp only [F]
  apply integral_congr_ae
  filter_upwards [dirichletL2_univ_ae g μ hμ u,dirichletL2_univ_ae g μ hμ v] with x hu hv
  rw [hu,hv]

theorem scalarClosedEnergy_eq_univ_differential (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (u v : ScalarEnergySpace g μ hμ) :
    scalarClosedEnergy g μ hμ u v=(1/2 : ℝ)*inner ℝ
      (scalarEnergyD g μ hμ Set.univ u) (scalarEnergyD g μ hμ Set.univ v) := by
  have he := dirichletEnergy_inner g μ hμ Set.univ
    (scalarEnergyUnivEquiv g μ hμ u) (scalarEnergyUnivEquiv g μ hμ v)
  rw [(scalarEnergyUnivEquiv g μ hμ).inner_map_map,dirichletL2_univ_inner] at he
  change inner ℝ u v=inner ℝ (scalarEnergyL2 g μ hμ u) (scalarEnergyL2 g μ hμ v)+
    (1/2 : ℝ)*inner ℝ (scalarEnergyD g μ hμ Set.univ u) (scalarEnergyD g μ hμ Set.univ v) at he
  unfold scalarClosedEnergy
  linarith only [he]

end Yau.Proofs.F03Aux
