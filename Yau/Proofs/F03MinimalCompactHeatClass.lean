import Yau.Proofs.F03MinimalCompactInitialJets
import Yau.Proofs.F03BoundedHeatEquation

/-! The original same-kernel integral lies in the full bounded scalar heat class for every true compact datum. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalBoundedHeat_compact_class
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (k : ScalarEnergyDomain g μ hμ) :
    IsBoundedScalarHeat g.form (fun y => k y)
      (boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => k y)) := by
  have hc := continuous_of_smoothFn k.2.1
  have hf : AEStronglyMeasurable (fun y => k y) μ := hc.aestronglyMeasurable
  obtain ⟨C,hC⟩ := hc.bounded_above_of_compact_support k.2.2
  let B := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBound : ∀ y,|k y| ≤ B := fun y =>
    (show |k y| ≤ C by simpa only [Real.norm_eq_abs] using hC y).trans (le_max_right _ _)
  exact ⟨dirichletMinimalBoundedHeat_smooth g hK μ hμ O hO (fun y => k y) hf B hB hBound,
    dirichletMinimalBoundedHeat_compact_smooth_initial g hK μ hμ O hO k,
    (fun _T _hT => ⟨B,hB,fun x t ht _htT =>
      (dirichletMinimalKernelCandidate_bounded_evolution_le g hK μ hμ O hO
        (fun y => k y) hf B hB.le hBound ht x).2⟩),
    (fun x t ht => dirichletMinimalBoundedHeat_hasDerivAt g hK μ hμ O hO
      (fun y => k y) hf B hB hBound x ht)⟩

end Yau.Proofs.F03Aux
