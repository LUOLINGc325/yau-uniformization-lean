import Yau.Proofs.F03BoundedHeatEquation
import Yau.Proofs.F03BoundedLocalizationRate

/-! The genuine far-source heat is homogeneous, vanishes initially on the cutoff region, and is O(t) there. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem dirichletMinimalBoundedHeat_far_source
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B)
    (η : ScalarEnergyDomain g μ hμ) (hηrange : ∀ y,η y ∈ Icc (0 : ℝ) 1) :
    let F := fun y => (1-η y)*f y
    let u := boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) F
    SmoothSpaceTime (fun x t => u t x) (Ioi 0) ∧
      (∀ x t,0 < t → HasDerivAt (fun s => u s x) (laplacian g.form (u t) x) t) ∧
      (∀ x,η x=1 → u 0 x=0) ∧
      ∃ C : ℝ,0 < C ∧ ∀ t,0 < t → ∀ x,η x=1 → |u t x| ≤ C*t := by
  let F := fun y => (1-η y)*f y
  let u := boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) F
  have hη : AEStronglyMeasurable (fun y => η y) μ :=
    (continuous_of_smoothFn η.2.1).aestronglyMeasurable
  have hF : AEStronglyMeasurable F μ := (aestronglyMeasurable_const.sub hη).mul hf
  have hFb : ∀ y,|F y| ≤ B := by
    intro y
    have hOne : |1-η y| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hηrange y).2)]
      linarith [(hηrange y).1]
    exact ((abs_mul (1-η y) (f y)).le.trans
      ((mul_le_mul_of_nonneg_right hOne (abs_nonneg _)).trans (by simpa using hBound y)))
  have hηfb : ∀ y,|η y*f y| ≤ B := by
    intro y
    rw [abs_mul,abs_of_nonneg (hηrange y).1]
    exact ((mul_le_mul_of_nonneg_right (hηrange y).2 (abs_nonneg _)).trans (by simpa using hBound y))
  refine ⟨dirichletMinimalBoundedHeat_smooth g hK μ hμ O hO F hF B hB hFb,
    (fun x t ht => dirichletMinimalBoundedHeat_hasDerivAt g hK μ hμ O hO F hF B hB hFb x ht),?_,?_⟩
  · intro x hx
    simp [u,boundedKernelEvolution,F,hx]
  · obtain ⟨C,hC,hRate⟩ := dirichletMinimalBoundedHeat_localization_rate g hK μ hμ O hO
      f hf B hB.le hBound η hηrange
    refine ⟨C,hC,fun t ht x hx => ?_⟩
    have hEq : u t x=
        boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x-
        boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => η y*f y) t x := by
      have hiF := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO
        f hf ⟨B,hBound⟩ ht x
      have hiηF := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO
        (fun y => η y*f y) (hη.mul hf) ⟨B,hηfb⟩ ht x
      simp only [u,boundedKernelEvolution,if_neg ht.ne']
      rw [← integral_sub hiF hiηF]
      apply integral_congr_ae
      exact ae_of_all μ (fun y => by dsimp [F];ring)
    exact (congrArg abs hEq).trans_le (hRate t ht x hx)

end Yau.Proofs.F03Aux
