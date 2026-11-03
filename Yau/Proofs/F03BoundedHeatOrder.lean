import Yau.Proofs.F03BoundedKernelAlgebra

/-! Actual order of the same minimal-kernel evolution, including the prescribed initial face. -/
noncomputable section
open MeasureTheory Filter Set
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletMinimalBoundedHeat_nonnegative
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : ∀ y,0 ≤ f y)
    {t : ℝ} (ht : 0 ≤ t) (x : M.Carrier) :
    0 ≤ boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x := by
  rcases eq_or_lt_of_le ht with ht0|ht0
  · subst t
    simpa [boundedKernelEvolution] using hf x
  · simp only [boundedKernelEvolution,if_neg ht0.ne']
    exact integral_nonneg (fun y => mul_nonneg
      (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht0 x y) (hf y))

theorem dirichletMinimalBoundedHeat_mono
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f q : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ) (hq : AEStronglyMeasurable q μ)
    (hfBounded : ∃ B : ℝ,∀ y,|f y| ≤ B) (hqBounded : ∃ B : ℝ,∀ y,|q y| ≤ B)
    (hOrder : ∀ y,f y ≤ q y) {t : ℝ} (ht : 0 ≤ t) (x : M.Carrier) :
    boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x ≤
      boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) q t x := by
  rcases eq_or_lt_of_le ht with ht0|ht0
  · subst t
    simpa [boundedKernelEvolution] using hOrder x
  · simp only [boundedKernelEvolution,if_neg ht0.ne']
    apply integral_mono
      (dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO f hf hfBounded ht0 x)
      (dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO q hq hqBounded ht0 x)
    intro y
    exact mul_le_mul_of_nonneg_left (hOrder y)
      (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht0 x y)

end Yau.Proofs.F03Aux
