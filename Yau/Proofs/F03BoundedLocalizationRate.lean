import Yau.Proofs.F03MinimalCompactEvolution
import Yau.Proofs.F03CompactHeatInitialRate
import Yau.Proofs.F03MinimalCutoffError

/-! The actual bounded-data localization error is O(t) wherever the compact cutoff is one. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalBoundedHeat_localization_rate
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ y,|f y| ≤ B)
    (η : ScalarEnergyDomain g μ hμ) (hηrange : ∀ y,η y ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ,0 < C ∧ ∀ t,0 < t → ∀ x,η x=1 →
      |boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x-
        boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
          (fun y => η y*f y) t x| ≤ C*t := by
  obtain ⟨K,hK0,hRate⟩ := wholeCompactHeat_initial_rate g hK μ hμ η
  let C := (B+1)*K
  have hC : 0 < C := mul_pos (by linarith) hK0
  refine ⟨C,hC,fun t ht x hηone => ?_⟩
  have hE := congrFun (dirichletMinimalKernelCandidate_compact_evolution g hK μ hμ O hO η ht) x
  rw [boundedKernelEvolution,if_neg ht.ne'] at hE
  have hCompact : |(∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*η y ∂μ)-1| ≤ t*K := by
    rw [hE]
    simpa only [hηone] using hRate t ht x
  have hError := dirichletMinimalKernelCandidate_cutoff_error g hK μ hμ O hO f η hf
    (continuous_of_smoothFn η.2.1).aestronglyMeasurable hηrange B hB hBound ht x
  simp only [boundedKernelEvolution,if_neg ht.ne']
  calc
    _ ≤ B*(1-∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*η y ∂μ) := hError
    _ ≤ B*|(∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*η y ∂μ)-1| := by
      apply mul_le_mul_of_nonneg_left _ hB
      rw [abs_sub_comm]
      exact le_abs_self _
    _ ≤ B*(t*K) := mul_le_mul_of_nonneg_left hCompact hB
    _ ≤ C*t := by dsimp [C];nlinarith [mul_pos ht hK0]

end Yau.Proofs.F03Aux
