import Yau.Proofs.D02PhysicalScaling
import Yau.Proofs.D02AreaReparamJacobian

/-! A holomorphic bijection of the open unit disc preserves the original
physical disc area. Its real Jacobian cancels the actual tangent scaling. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02AreaReparamAux
open Yau Yau.Blueprint Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

theorem physicalCurveDerivative_comp {n : ℕ} {M : ComplexManifold n}
    {f : ℂ → M.Carrier} {α : ℂ → ℂ} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (ComplexModel n) f (α z))
    (hα : DifferentiableAt ℂ α z) :
    physicalCurveDerivative (f ∘ α) z = deriv α z • physicalCurveDerivative f (α z) := by
  have hc := mfderiv_comp_apply z hf hα.mdifferentiableAt
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)
  have hα' : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) α z
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1) =
      deriv α z • ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (α z)).symm 1) := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℂ α z 1 = deriv α z * 1
    rw [fderiv_apply_one_eq_deriv, mul_one]
  rw [hα', map_smul] at hc
  exact hc

theorem discArea_comp_of_bijOn {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    {α : ℂ → ℂ} (hα : DifferentiableOn ℂ α (ball (0 : ℂ) 1))
    (hbij : BijOn α (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    discArea g (f ∘ α) = discArea g f := by
  let A : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv α z)).restrictScalars ℝ
  have hA (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasFDerivWithinAt α (A z) (ball (0 : ℂ) 1) z :=
    (((hα.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  let q : ℂ → ENNReal := fun w =>
    ENNReal.ofReal (hermitianNormSq (g (f w)) (physicalCurveDerivative f w))
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ)
    measurableSet_ball hA hbij.injOn q
  rw [hbij.image_eq] at hchange
  change (2 : ENNReal) * (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal
      (hermitianNormSq (g ((f ∘ α) z)) (physicalCurveDerivative (f ∘ α) z))) =
    2 * (∫⁻ z in ball (0 : ℂ) 1, q z)
  congr 1
  rw [hchange]
  apply setLIntegral_congr_fun measurableSet_ball
  intro z hz
  have hαz := hα.differentiableAt (isOpen_ball.mem_nhds hz)
  have hfz := (hf.contMDiffAt (mem_of_superset (isOpen_ball.mem_nhds (hbij.mapsTo hz))
    ball_subset_closedBall)).mdifferentiableAt (by simp)
  dsimp only []
  rw [physicalCurveDerivative_comp hfz hαz, Yau.NodeProofs.G01Aux.hermitianNormSq_smul]
  rw [ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
  have hd : |(A z).det| = Complex.normSq (deriv α z) := by
    rw [complex_scalar_real_det, abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [hd]
  rfl

end Yau.NodeProofs.D02AreaReparamAux
