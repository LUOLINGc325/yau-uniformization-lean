import Yau.Proofs.C05GradientFlowTrapping
import Yau.Proofs.C05GradientFlowContraction
import Yau.Proofs.C05GradientFlowJointContinuity
import Yau.Proofs.C05CompactInvariantFlow

/-! A genuine contracting all-forward gradient flow on the compact intrinsic trap. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem exists_contracting_gradient_flow (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier) (a r : ℝ)
    (ha : 0 < a) (hr : 0 < r)
    (hHess : ∀ x ∈ distBall g.form o (2 * r), ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (hgrad : realNorm g.form o (realGrad g.form f o) ≤ a * r / 8) :
    letI := manifold_realSmooth M
    ∃ F : ℝ → M.Carrier → M.Carrier,
      (∀ x ∈ gradientTrap g o r, F 0 x = x) ∧
      (∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, F t x ∈ gradientTrap g o r) ∧
      (∀ x ∈ gradientTrap g o r, ∀ t, 0 ≤ t →
        IsMIntegralCurveAt (fun s => F s x) (realGradientVectorField g.form f) t) ∧
      ContinuousOn (fun p : ℝ × M.Carrier => F p.1 p.2)
        (Set.Ici 0 ×ˢ gradientTrap g o r) ∧
      (∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, ∀ y ∈ gradientTrap g o r,
        inducedDistance g.form (F t x) (F t y) ≤
          Real.exp (-a * t) * inducedDistance g.form x y) := by
  letI := manifold_realSmooth M
  obtain ⟨F, hF0, hFK, hIC, htime⟩ :=
    C05CompactInvariantFlowAux.exists_forward_integral_curves_of_compact_local_invariant
      (realGradientVectorField g.form f) (realGradientVectorField_contMDiff g f hf)
      (gradientTrap g o r) (gradientTrap_isCompact g o r)
      (fun γ ε hε h0 hγ => gradient_local_forward_invariant g f hf o a r ha hr hHess hgrad
        γ ε hε h0 hγ)
  have hcontract : ∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, ∀ y ∈ gradientTrap g o r,
      inducedDistance g.form (F t x) (F t y) ≤
        Real.exp (-a * t) * inducedDistance g.form x y := by
    intro t ht x hx y hy
    have H := gradient_integral_curves_contraction g f hf o a r ha hr hHess
      (fun s => F s x) (fun s => F s y) (hFK x hx) (hFK y hy) (hIC x hx) (hIC y hy) t ht
    simpa only [hF0 x hx, hF0 y hy] using H
  have hspace : ∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, ∀ y ∈ gradientTrap g o r,
      inducedDistance g.form (F t x) (F t y) ≤ inducedDistance g.form x y := by
    intro t ht x hx y hy
    have hexp : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg ha.le ht))
    exact (hcontract t ht x hx y hy).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (g.induced_distance_nonneg x y))
  exact ⟨F, hF0, (fun t ht x hx => hFK x hx t ht), hIC,
    joint_continuousOn_of_time_continuous_nonexpansive g F (gradientTrap g o r) htime hspace,
    hcontract⟩

end Yau.Proofs.C05GradientFlowAux
