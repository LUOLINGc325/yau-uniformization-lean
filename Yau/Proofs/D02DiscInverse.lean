import Yau.Proofs.D02ImmersionInverse
import Yau.Proofs.D02AreaDensity
import Yau.Proofs.D02ImmersionBoundary

/-! The same actual disc derivative satisfies the inverse-Jacobian
energy estimate, expressed through the actual holomorphic immersion image. -/

open scoped Manifold Topology ContDiff ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

theorem immersionDisc_derivative {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (f z)))
      (mfderiv (ComplexModel n) (ComplexModel N) F (f z) (physicalCurveDerivative f z)) =
        deriv (fun w => F (f w)) z := by
  have hn : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hd := (hf.contMDiffAt hn).mdifferentiableAt (by simp)
  have hc := mfderiv_comp_apply z (hF (f z)) hd
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)
  rw [mfderiv_eq_fderiv] at hc
  have hc' := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (f z))) hc
  have hone : (NormedSpace.fromTangentSpace (𝕜 := ℂ) z)
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1) = 1 := rfl
  simpa [physicalCurveDerivative, mfld_simps, fderiv_apply_one_eq_deriv, hone,
    Function.comp_def] using hc'.symm

theorem discDensity_inverse_bound (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (B : ℝ)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (hu : immersionDifferentialNormSq g F (f z) ≤ B) :
    closedDiscDensity g f z ≤ 2 * max 1 B ^ (n - 1) * Real.exp (-immersionPotential g F (f z)) *
      ‖deriv (fun w => F (f w)) z‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (immersionDerivative_inverse_bound g hF hImm B (f z) hu (physicalCurveDerivative f z))
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [immersionDisc_derivative hF hf hz] at h
  rw [closedDiscDensity_eq_physical g hf hz]
  simpa only [mul_assoc] using h

end Yau.NodeProofs.D02Aux
