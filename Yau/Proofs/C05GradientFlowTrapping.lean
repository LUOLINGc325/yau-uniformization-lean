import Yau.Proofs.C05GradientFlowRadialDistance

/-! Strict inward radial distance slope traps every actual local gradient solution. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem gradient_local_forward_invariant (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier) (a r : ℝ)
    (ha : 0 < a) (hr : 0 < r)
    (hHess : ∀ x ∈ distBall g.form o (2 * r), ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (hgrad : realNorm g.form o (realGrad g.form f o) ≤ a * r / 8)
    (γ : ℝ → M.Carrier) (ε : ℝ) (hε : 0 < ε)
    (h0 : γ 0 ∈ gradientTrap g o r) :
    letI := manifold_realSmooth M
    IsMIntegralCurveOn γ (realGradientVectorField g.form f) (Set.Ioo (-ε) ε) →
      ∀ t ∈ Set.Ico (0 : ℝ) ε, γ t ∈ gradientTrap g o r := by
  letI := manifold_realSmooth M
  intro hγ t ht
  let u := fun s => inducedDistance g.form o (γ s)
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ioo (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩
  have hu : ContinuousOn u (Set.Icc (0 : ℝ) t) :=
    (continuous_inducedDistance g).comp_continuousOn
      (continuousOn_const.prodMk (hγ.continuousOn.mono hsub))
  have hboundary : ∀ s ∈ Set.Ico (0 : ℝ) t, u s = r / 2 →
      ∃ d : ℝ, d < 0 ∧ UpperRightSlopeLE u s d := by
    intro s hs heq
    have hsε := hsub (Set.Ico_subset_Icc_self hs)
    have hD : 0 < inducedDistance g.form o (γ s) := by
      change 0 < u s
      rw [heq]
      positivity
    have hball : γ s ∈ distBall g.form o (2 * r) := by
      apply (mem_distBall_iff g o _ (by positivity)).mpr
      change u s < 2 * r
      rw [heq]
      linarith
    refine ⟨realNorm g.form o (realGrad g.form f o) - a * u s, ?_, ?_⟩
    · rw [heq]
      nlinarith only [hgrad, mul_pos ha hr]
    · exact gradient_radial_distance_upperRightSlopeLE g f hf o a r hr hHess γ s hD hball
        (hγ.isMIntegralCurveAt (Ioo_mem_nhds hsε.1 hsε.2))
  exact boundary_fence u hu h0 hboundary ⟨ht.1, le_rfl⟩

end Yau.Proofs.C05GradientFlowAux
