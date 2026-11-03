import Yau.Proofs.F03MinimalBoundedEvolution

/-! Actual bounded-source kernel evolution is additive, including the prescribed initial value. -/
noncomputable section
open MeasureTheory Filter Set
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletMinimalBoundedHeat_add
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f k : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ) (hk : AEStronglyMeasurable k μ)
    (hfb : ∃ B : ℝ,∀ y,|f y| ≤ B) (hkb : ∃ B : ℝ,∀ y,|k y| ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => f y+k y) t=
      (fun x => boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x+
        boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) k t x) := by
  by_cases ht0 : t=0
  · subst t
    funext x
    simp [boundedKernelEvolution]
  · have htPos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    funext x
    have hiF := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO f hf hfb htPos x
    have hiK := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO k hk hkb htPos x
    simp only [boundedKernelEvolution,if_neg ht0]
    rw [← integral_add hiF hiK]
    apply integral_congr_ae
    exact ae_of_all μ (fun y => by ring)

end Yau.Proofs.F03Aux
