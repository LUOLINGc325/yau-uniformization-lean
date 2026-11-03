import Yau.Proofs.F04AmbientShiftDifferential

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletAmbientShiftPosPart_pairings
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    let w := dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq
    inner ℝ (dirichletL2 g μ hμ O u - l2Restriction μ O (scalarEnergyL2 g μ hμ q))
        (dirichletL2 g μ hμ O w) = ‖dirichletL2 g μ hμ O w‖ ^ 2 ∧
      inner ℝ (dirichletD g μ hμ O u - scalarEnergyD g μ hμ O q)
        (dirichletD g μ hμ O w) = ‖dirichletD g μ hμ O w‖ ^ 2 := by
  dsimp only
  constructor
  · rw [dirichletAmbientShiftPosPart_L2]
    exact l2_posPart_pairing (μ.restrict O) _
  · rw [dirichletAmbientShiftPosPart_D]
    exact positiveFormMultiplier_pairing g (μ.restrict O) _ _

/-- The same genuine test has the exact coercive projection pairing on the
whole manifold, needed for domain-to-ambient resolvent domination. -/
theorem dirichletAmbientShiftPosPart_global_pairings
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (u : DirichletEnergy g μ hμ O) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x) :
    let w := dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq
    inner ℝ (scalarEnergyL2 g μ hμ u.val - scalarEnergyL2 g μ hμ q)
        (scalarEnergyL2 g μ hμ w.val) = ‖scalarEnergyL2 g μ hμ w.val‖ ^ 2 ∧
      inner ℝ (scalarEnergyD g μ hμ Set.univ u.val - scalarEnergyD g μ hμ Set.univ q)
        (scalarEnergyD g μ hμ Set.univ w.val) = ‖scalarEnergyD g μ hμ Set.univ w.val‖ ^ 2 := by
  let w := dirichletAmbientShiftPosPart g hK μ hμ O hO u q hq
  have hJ : scalarEnergyL2 g μ hμ w.val =
      Lp.posPart (scalarEnergyL2 g μ hμ u.val - scalarEnergyL2 g μ hμ q) :=
    dirichletAmbientShiftPosPart_ambient_L2 g hK μ hμ O hO u q hq
  have hglobal : scalarEnergyL2 g μ hμ w.val =
      Lp.posPart (scalarEnergyL2 g μ hμ (u.val - q)) := by
    simpa only [map_sub] using hJ
  let f := dirichletL2 g μ hμ Set.univ (scalarEnergyUnivEquiv g μ hμ (u.val - q))
  have hc : scalarEnergyD g μ hμ Set.univ w.val =
      positiveFormMultiplier g (μ.restrict Set.univ) f (scalarEnergyD g μ hμ Set.univ (u.val - q)) :=
    scalarEnergyD_positive_of_ambient_eq g hK μ hμ w.val (u.val - q) hglobal
  have he := (scalarEnergyD g μ hμ Set.univ).map_sub u.val q
  have hD : scalarEnergyD g μ hμ Set.univ w.val =
      positiveFormMultiplier g (μ.restrict Set.univ) f
        (scalarEnergyD g μ hμ Set.univ u.val - scalarEnergyD g μ hμ Set.univ q) :=
    hc.trans (congrArg (positiveFormMultiplier g (μ.restrict Set.univ) f) he)
  change inner ℝ (scalarEnergyL2 g μ hμ u.val - scalarEnergyL2 g μ hμ q)
      (scalarEnergyL2 g μ hμ w.val) = ‖scalarEnergyL2 g μ hμ w.val‖ ^ 2 ∧
    inner ℝ (scalarEnergyD g μ hμ Set.univ u.val - scalarEnergyD g μ hμ Set.univ q)
      (scalarEnergyD g μ hμ Set.univ w.val) = ‖scalarEnergyD g μ hμ Set.univ w.val‖ ^ 2
  constructor
  · rw [hJ]
    exact l2_posPart_pairing μ _
  · rw [hD]
    exact positiveFormMultiplier_pairing g (μ.restrict Set.univ) f
      (scalarEnergyD g μ hμ Set.univ u.val - scalarEnergyD g μ hμ Set.univ q)

end Yau.F04Proof
