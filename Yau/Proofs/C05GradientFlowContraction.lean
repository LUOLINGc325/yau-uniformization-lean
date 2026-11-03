import Yau.Proofs.C05GradientFlowPairDistance

/-! The same actual gradient curves contract by the exact factor exp (-a t). -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem gradient_integral_curves_contraction (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier) (a r : ℝ)
    (ha : 0 < a) (hr : 0 < r)
    (hHess : ∀ x ∈ distBall g.form o (2 * r), ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (α β : ℝ → M.Carrier)
    (hαK : ∀ t, 0 ≤ t → α t ∈ gradientTrap g o r)
    (hβK : ∀ t, 0 ≤ t → β t ∈ gradientTrap g o r) :
    letI := manifold_realSmooth M
    (∀ t, 0 ≤ t → IsMIntegralCurveAt α (realGradientVectorField g.form f) t) →
    (∀ t, 0 ≤ t → IsMIntegralCurveAt β (realGradientVectorField g.form f) t) →
    ∀ t, 0 ≤ t → inducedDistance g.form (α t) (β t) ≤
      Real.exp (-a * t) * inducedDistance g.form (α 0) (β 0) := by
  letI := manifold_realSmooth M
  intro hα hβ t ht
  let u := fun s => inducedDistance g.form (α s) (β s)
  have hu : ContinuousOn u (Set.Icc (0 : ℝ) t) := by
    have hαc : ContinuousOn α (Set.Icc (0 : ℝ) t) :=
      fun s hs => (hα s hs.1).continuousAt.continuousWithinAt
    have hβc : ContinuousOn β (Set.Icc (0 : ℝ) t) :=
      fun s hs => (hβ s hs.1).continuousAt.continuousWithinAt
    exact (continuous_inducedDistance g).comp_continuousOn (hαc.prodMk hβc)
  have hD : ∀ s ∈ Set.Ico (0 : ℝ) t, UpperRightSlopeLE u s (-a * u s) := by
    intro s hs
    exact gradient_pair_distance_upperRightSlopeLE g f hf o a r hr hHess α β s
      (hαK s hs.1) (hβK s hs.1) (hα s hs.1) (hβ s hs.1)
  simpa only [u, sub_zero] using upperRightSlopeLE_exponential_decay u ha hu hD ⟨ht, le_rfl⟩

end Yau.Proofs.C05GradientFlowAux
