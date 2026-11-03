import Yau.Proofs.F04AmbientEnergy
import Yau.Proofs.F04PositiveDifferential

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletUniv_posPart_of_ambient_eq
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (p q : ScalarEnergySpace g μ hμ)
    (hpos : scalarEnergyL2 g μ hμ p = Lp.posPart (scalarEnergyL2 g μ hμ q)) :
    scalarEnergyUnivEquiv g μ hμ p =
      dirichletPosPart g μ hμ Set.univ MeasurableSet.univ (scalarEnergyUnivEquiv g μ hμ q) := by
  apply dirichletL2_injective g hK μ hμ Set.univ MeasurableSet.univ
  rw [(dirichletPosPart_spec g μ hμ Set.univ MeasurableSet.univ _).1]
  have hpa : ∀ᵐ x ∂μ, scalarEnergyL2 g μ hμ p x = max (scalarEnergyL2 g μ hμ q x) 0 := by
    rw [hpos]
    exact Lp.coeFn_posPart _
  apply Lp.ext
  filter_upwards [ae_restrict_of_ae (dirichletL2_univ_ae g μ hμ p),
    ae_restrict_of_ae (dirichletL2_univ_ae g μ hμ q), ae_restrict_of_ae hpa,
    Lp.coeFn_posPart (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ q))]
    with x hp hq hpa hpp
  rw [hp, hpp, hq, hpa]

theorem scalarEnergyD_positive_of_ambient_eq
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (p q : ScalarEnergySpace g μ hμ)
    (hpos : scalarEnergyL2 g μ hμ p = Lp.posPart (scalarEnergyL2 g μ hμ q)) :
    scalarEnergyD g μ hμ Set.univ p =
      positiveFormMultiplier g (μ.restrict Set.univ)
        (dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ q))
        (scalarEnergyD g μ hμ Set.univ q) := by
  change dirichletD g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ p) = _
  rw [dirichletUniv_posPart_of_ambient_eq g hK μ hμ p q hpos,
    dirichletPosPart_D g hK μ hμ Set.univ MeasurableSet.univ]
  rfl

end Yau.F04Proof
