import Yau.Proofs.C05GradientFlowGeodesicHessian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Hessian bounds integrate along the same genuine minimizing segment. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem scalarVelocity_geodesic_difference_le (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (a : ℝ) (U : Set M.Carrier)
    (hHess : ∀ x ∈ U, ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, (realGeodesicFlow g p t).proj ∈ U) :
    scalarVelocity f (realGeodesicFlow g p 1) - scalarVelocity f p ≤
      -a * realTangentEnergy g.form p := by
  let q := fun t => scalarVelocity f (realGeodesicFlow g p t)
  have hq (t : ℝ) := scalarVelocity_realGeodesic_hasDerivAt g f hf p t
  have hcont : ContinuousOn q (Set.Icc (0 : ℝ) 1) :=
    fun t _ => (hq t).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ q (interior (Set.Icc (0 : ℝ) 1)) :=
    fun t _ => (hq t).differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      deriv q t ≤ -a * realTangentEnergy g.form p := by
    intro t ht
    rw [(hq t).deriv]
    have H := hHess _ (hU t (interior_subset ht))
      (realTangentEquiv _ (realGeodesicFlow g p t).2)
    rwa [realNormSq_realGeodesic_velocity] at H
  have H := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hbound 0 (by simp) 1 (by simp) zero_le_one
  simpa only [q, realGeodesicFlow_zero, sub_zero, mul_one] using H

theorem scalarVelocity_le_gradient_norm (k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    scalarVelocity f p ≤ realNorm k p.proj (realGrad k f p.proj) *
      Real.sqrt (realTangentEnergy k p) := by
  letI := underlyingRealTangentNormedAddCommGroup k p.proj
  letI := underlyingRealTangentInnerProductSpace k p.proj
  rw [scalarVelocity, ← realGradientVectorField_dual k f hf]
  have H := real_inner_le_norm (realGradientVectorField k f p.proj) p.2
  change (underlyingRealRiemannianMetric k).inner p.proj
    (realGradientVectorField k f p.proj) p.2 ≤
      ‖realGradientVectorField k f p.proj‖ * ‖p.2‖ at H
  rw [realGradientVectorField_norm] at H
  convert H using 1
  rw [realTangentEnergy_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem scalarVelocity_geodesic_terminal_le (g : SmoothMetric M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (a : ℝ) (U : Set M.Carrier)
    (hHess : ∀ x ∈ U, ∀ v : TangentVector M x,
      realHess g.form f x v v ≤ -a * realNormSq g.form x v)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, (realGeodesicFlow g p t).proj ∈ U) :
    scalarVelocity f (realGeodesicFlow g p 1) ≤
      realNorm g.form p.proj (realGrad g.form f p.proj) *
        Real.sqrt (realTangentEnergy g.form p) - a * realTangentEnergy g.form p := by
  linarith [scalarVelocity_geodesic_difference_le g f hf a U hHess p hU,
    scalarVelocity_le_gradient_norm g.form f hf p]

end Yau.Proofs.C05GradientFlowAux
