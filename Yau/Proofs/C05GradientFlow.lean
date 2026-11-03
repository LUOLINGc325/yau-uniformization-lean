import Yau.Proofs.C05GradientFlowCore
import Yau.Proofs.C05GradientFlowLoopTransport
import Yau.Proofs.C05GradientFlowNorm

/-! Genuine complete-metric gradient contraction and continuous loop contraction.
The Hessian and center-gradient bounds are natural intermediate hypotheses,
discharged from the original Harnack inlet by its owner. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem loop_nullhomotopic_of_hessian_negative (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier) (a r : ℝ)
    (ha : 0 < a) (hr : 0 < r)
    (hHess : ∀ x ∈ distBall g.form o (2 * r), ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (hgrad : realNorm g.form o (realGrad g.form f o) ≤ a * r / 8)
    {x : M.Carrier} (γ : Path x x) (hγ : ∀ u, γ u ∈ gradientTrap g o r) :
    γ.Homotopic (Path.refl x) := by
  letI := manifold_realSmooth M
  obtain ⟨F, hF0, hFK, _, hcont, hcontract⟩ :=
    exists_contracting_gradient_flow g f hf o a r ha hr hHess hgrad
  exact loop_nullhomotopic_of_contracting_family g o a r ha hr F hF0 hFK hcont hcontract γ hγ

end Yau.Proofs.C05GradientFlowAux
