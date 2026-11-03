import Yau.Proofs.D02AreaScaling

/-! The physical weighted energy, with its exact rescaling constant. -/

open scoped ENNReal Manifold Topology
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def physicalWeightedEnergy (g : HermitianField M) (h : ℂ → M.Carrier) (ρ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ},
    ENNReal.ofReal (hermitianNormSq (g (h z)) (physicalCurveDerivative h z) * ‖z‖ ^ (-σ)) ∂volume

theorem physicalWeightedEnergy_rescale (g : HermitianField M) (h : ℂ → M.Carrier)
    (R : ℝ) (hR : 0 < R) (ρ σ : ℝ)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h
      {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R * ρ}) :
    physicalWeightedEnergy g (rescaledCurve h 0 R) ρ σ =
      ENNReal.ofReal (R ^ σ) * physicalWeightedEnergy g h (R * ρ) σ := by
  have hS : IsOpen {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R * ρ} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hzR {z : ℂ} (hz : 0 < ‖z‖ ∧ ‖z‖ < ρ) :
      0 < ‖R • z‖ ∧ ‖R • z‖ < R * ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    refine ⟨mul_pos hR hz.1, ?_⟩
    nlinarith
  have hleft : physicalWeightedEnergy g (rescaledCurve h 0 R) ρ σ =
      ∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ}, ENNReal.ofReal (R ^ 2) *
        ENNReal.ofReal (hermitianNormSq (g (h (R • z))) (physicalCurveDerivative h (R • z))) *
          ENNReal.ofReal (‖z‖ ^ (-σ)) ∂volume := by
    apply setLIntegral_congr_fun
      (((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).measurableSet :
        MeasurableSet {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ})
    intro z hz
    have hh' := hh.mdifferentiableAt (hS.mem_nhds (hzR hz))
    have hd := rescaledCurve_energyDensity g h 0 R z
      (by simpa only [zero_add, Complex.real_smul] using hh')
    have he : hermitianNormSq (g (rescaledCurve h 0 R z))
        (physicalCurveDerivative (rescaledCurve h 0 R) z) =
        R ^ 2 * hermitianNormSq (g (h (R • z))) (physicalCurveDerivative h (R • z)) := by
      have hz : (0 : ℂ) + (R : ℂ) * z = R • z := by simp [Complex.real_smul]
      change hermitianNormSq (g (rescaledCurve h 0 R z))
        (physicalCurveDerivative (rescaledCurve h 0 R) z) =
        R ^ 2 * hermitianNormSq (g (h ((0 : ℂ) + (R : ℂ) * z)))
          (physicalCurveDerivative h ((0 : ℂ) + (R : ℂ) * z)) at hd
      rw [hz] at hd
      exact hd
    dsimp only []
    rw [he, ENNReal.ofReal_mul (mul_nonneg (sq_nonneg R) (hermitianNormSq_nonneg _ _)),
      ENNReal.ofReal_mul (sq_nonneg R)]
  rw [hleft, weighted_setLIntegral_rescale R hR ρ σ
    (fun w => ENNReal.ofReal (hermitianNormSq (g (h w)) (physicalCurveDerivative h w)))]
  unfold physicalWeightedEnergy
  congr 1
  apply setLIntegral_congr_fun hS.measurableSet
  intro z _
  dsimp only []
  rw [ENNReal.ofReal_mul (hermitianNormSq_nonneg _ _)]

end Yau.NodeProofs.D02Aux
