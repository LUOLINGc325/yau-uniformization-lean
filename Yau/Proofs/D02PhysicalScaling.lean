import Yau.Proofs.D02PullbackSection
import Yau.Proofs.G01RmAlgebra

/-! Physical derivatives under actual affine parameter rescaling. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def physicalCurveDerivative (h : ℂ → M.Carrier) (z : ℂ) : TangentVector M (h z) :=
  mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h z
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)

def rescaledCurve (h : ℂ → M.Carrier) (z₀ : ℂ) (R : ℝ) (z : ℂ) : M.Carrier :=
  h (z₀ + (R : ℂ) * z)

theorem rescaledCurve_derivative (h : ℂ → M.Carrier) (z₀ : ℂ) (R : ℝ) (z : ℂ)
    (hh : MDifferentiableAt 𝓘(ℂ, ℂ) (ComplexModel n) h (z₀ + (R : ℂ) * z)) :
    physicalCurveDerivative (rescaledCurve h z₀ R) z =
      (R : ℂ) • physicalCurveDerivative h (z₀ + (R : ℂ) * z) := by
  let α : ℂ → ℂ := fun w => z₀ + (R : ℂ) * w
  have ha : HasDerivAt α (R : ℂ) z := (hasDerivAt_const_mul (R : ℂ)).const_add z₀
  have hm : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) α z := ha.differentiableAt.mdifferentiableAt
  have hc := mfderiv_comp_apply z hh hm ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)
  have hα : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) α z
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1) =
        (R : ℂ) • ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (α z)).symm 1) := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℂ α z 1 = (R : ℂ) * 1
    rw [fderiv_apply_one_eq_deriv, ha.deriv, mul_one]
  rw [hα, map_smul] at hc
  exact hc

theorem rescaledCurve_energyDensity (g : HermitianField M) (h : ℂ → M.Carrier)
    (z₀ : ℂ) (R : ℝ) (z : ℂ)
    (hh : MDifferentiableAt 𝓘(ℂ, ℂ) (ComplexModel n) h (z₀ + (R : ℂ) * z)) :
    hermitianNormSq (g (rescaledCurve h z₀ R z))
      (physicalCurveDerivative (rescaledCurve h z₀ R) z) =
      R ^ 2 * hermitianNormSq (g (h (z₀ + (R : ℂ) * z)))
        (physicalCurveDerivative h (z₀ + (R : ℂ) * z)) := by
  rw [rescaledCurve_derivative h z₀ R z hh, Yau.NodeProofs.G01Aux.hermitianNormSq_smul]
  simp only [Complex.normSq_ofReal, rescaledCurve]
  ring

end Yau.NodeProofs.D02Aux
