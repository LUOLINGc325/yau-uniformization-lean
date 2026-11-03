import Yau.Proofs.D03ClosureSubmoduleLocal

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter Metric Bundle

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

/-- A scalar germ has an actual analytic representative bounded on a smaller disc. -/
theorem closure_analyticGerm_bounded (a : AnalyticGerm) :
    ∃ f : ℂ → ℂ, ∃ hf : AnalyticAt ℂ f 0, ∃ R B : ℝ,
      0 < R ∧ 0 ≤ B ∧ DifferentiableOn ℂ f (ball 0 R) ∧
      (∀ z ∈ ball 0 R, ‖f z‖ ≤ B) ∧ ofAnalytic f hf = a := by
  let f := analyticRepresentative a
  have hf : AnalyticAt ℂ f 0 := analyticRepresentative_analytic a
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have hd : DifferentiableOn ℂ f (ball 0 ε) :=
    fun z hz => (hball hz).differentiableAt.differentiableWithinAt
  have hsub : closedBall (0 : ℂ) (ε / 2) ⊆ ball 0 ε :=
    closedBall_subset_ball (by linarith)
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : ℂ) (ε / 2)).exists_isMaxOn
    (show (closedBall (0 : ℂ) (ε / 2)).Nonempty from ⟨0, mem_closedBall_self (by positivity)⟩)
    (hd.continuousOn.mono hsub).norm
  refine ⟨f, hf, ε / 2, ‖f z‖, by positivity, norm_nonneg _, hd.mono (ball_subset_ball (by linarith)), ?_, ?_⟩
  · intro w hw
    exact hmax (ball_subset_closedBall hw)
  · exact ofAnalytic_representative a

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem closure_scalar_inChart_differentiableOn (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (f : ℂ → ℂ) (R : ℝ) (hf : DifferentiableOn ℂ f (ball 0 R))
    (ρ : ℝ) (hρR : ρ ≤ R) (a : M.Carrier) :
    DifferentiableOn ℂ (fun w => f (c (chartInv a w)))
      (BundleDbar.localDomain (r := r) E a ∩ (chartInv a) ⁻¹' discSectionDomain c ρ) := by
  intro w hw
  have hz : c (chartInv a w) ∈ ball 0 R := by
    rw [mem_ball_zero_iff]
    exact hw.2.2.trans_le hρR
  exact ((hf.differentiableAt (isOpen_ball.mem_nhds hz)).comp w
    ((B01Aux.disc_inChart_contDiffAt c hc a hw.1.1).differentiableAt (by simp))).differentiableWithinAt

theorem closure_holomorphicSectionOn_scalar (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (f : ℂ → ℂ) (R : ℝ) (hf : DifferentiableOn ℂ f (ball 0 R))
    (ρ : ℝ) (hρR : ρ ≤ R) (b : Section E)
    (hb : HolomorphicSectionOn (r := r) E b (discSectionDomain c ρ)) :
    HolomorphicSectionOn (r := r) E (fun x => f (c x) • b x) (discSectionDomain c ρ) :=
  holomorphicSectionOn_smul E (fun x => f (c x)) hb
    (closure_scalar_inChart_differentiableOn E c hc f R hf ρ hρR)

end Yau.Proofs.D03Aux
