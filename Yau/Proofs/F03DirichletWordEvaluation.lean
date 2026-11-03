import Yau.Proofs.F03DirichletLocalJetBound

/-! Actual bounded source evaluation of every finite interior heat word. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Source linearity comes from the already proved actual compact jet
map on a singleton; boundedness comes from the genuine local jet estimate. -/
def dirichletChartWordEvaluation (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (w : List (Parabolic.Point n)) (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :
    Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ := by
  let K : Set (Parabolic.Point n) := {p}
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_singleton
  have hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ) :=
    singleton_subset_iff.mpr hp
  let T : Lp ℝ 2 (μ.restrict Ω) →ₗ[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ (⟨p,mem_singleton p⟩ : K)).toLinearMap.comp
      (dirichletCompactHeatJet g hK μ hμ Ω hΩ a K hKQ w)
  let hc := dirichletClassicalChartHeat_local_jet_bound g hK μ hμ Ω hΩ a p hp
  let hw := hc.choose_spec.2.2 w
  exact T.mkContinuous hw.choose (by
    intro f
    change |directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w p| ≤ _
    exact hw.choose_spec.2 f p (Metric.mem_ball_self hc.choose_spec.1))

theorem dirichletChartWordEvaluation_apply (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (w : List (Parabolic.Point n)) (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    dirichletChartWordEvaluation g hK μ hμ Ω hΩ a w p hp f =
      directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w p := rfl

/-- Total zero extension is used only to state ordinary chart smoothness
on the actual positive-time interior. -/
def dirichletChartWordOperator (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (w : List (Parabolic.Point n)) (p : Parabolic.Point n) :
    Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ := by
  classical
  exact if hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ) then
    dirichletChartWordEvaluation g hK μ hμ Ω hΩ a w p hp else 0

theorem dirichletChartWordOperator_apply (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (w : List (Parabolic.Point n)) (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    dirichletChartWordOperator g hK μ hμ Ω hΩ a w p f =
      directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w p := by
  classical
  simp only [dirichletChartWordOperator,dif_pos hp,dirichletChartWordEvaluation_apply]

theorem dirichletChartWordOperator_local_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    (p : Parabolic.Point n)
    (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.ball p δ ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ) ∧
      ∀ w : List (Parabolic.Point n), ∃ C : ℝ, ∀ q ∈ Metric.ball p δ,
        ‖dirichletChartWordOperator g hK μ hμ Ω hΩ a w q‖ ≤ C := by
  obtain ⟨δ,hδ,hδQ,hBound⟩ := dirichletClassicalChartHeat_local_jet_bound g hK μ hμ Ω hΩ a p hp
  refine ⟨δ,hδ,hδQ,?_⟩
  intro w
  obtain ⟨C,hC,hCbound⟩ := hBound w
  refine ⟨C,?_⟩
  intro q hq
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro f
  rw [dirichletChartWordOperator_apply g hK μ hμ Ω hΩ a w q (hδQ hq),Real.norm_eq_abs]
  exact hCbound f q hq

end Yau.Proofs.F03Aux
