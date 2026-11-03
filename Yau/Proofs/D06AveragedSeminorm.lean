import Yau.Proofs.D06Seminorm

/-! The exact two-variable boundary seminorm as an integral of averaged
translation differences. This permits the factor one-half to be established
before integration against the singular kernel. -/

open scoped Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

variable {r : ℕ}

theorem continuous_frobSq : Continuous (frobSq : Matrix (Fin r) (Fin r) ℂ → ℝ) := by
  unfold frobSq
  fun_prop

def angularDifference (a : ℝ → Matrix (Fin r) (Fin r) ℂ) (θ : ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi), frobSq (a (t + θ) - a t)

def angularKernel (θ : ℝ) : ENNReal :=
  ENNReal.ofReal ((‖Complex.exp (θ * Complex.I) - 1‖ ^ 2)⁻¹)

theorem halfSobolevSq_eq_lintegral_angularDifference
    (a : ℝ → Matrix (Fin r) (Fin r) ℂ) (ha : Continuous a) :
    halfSobolevSq a = ENNReal.ofReal ((2 * Real.pi) ^ 2)⁻¹ *
      ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
        angularKernel θ * ENNReal.ofReal (angularDifference a θ) := by
  have hcurve : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hnum : Continuous (fun p : ℝ × ℝ => frobSq (a (p.1 + p.2) - a p.1)) :=
    continuous_frobSq.comp
      ((ha.comp (continuous_fst.add continuous_snd)).sub (ha.comp continuous_fst))
  have hden : Continuous (fun p : ℝ × ℝ => ‖Complex.exp (p.2 * Complex.I) - 1‖ ^ 2) :=
    ((hcurve.comp continuous_snd).sub continuous_const).norm.pow 2
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (frobSq (a (p.1 + p.2) - a p.1) / ‖Complex.exp (p.2 * Complex.I) - 1‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hnum.measurable.div hden.measurable)
  unfold halfSobolevSq
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  congr 1
  apply lintegral_congr
  intro θ
  have hcont : Continuous (fun t : ℝ => frobSq (a (t + θ) - a t)) :=
    continuous_frobSq.comp ((ha.comp (continuous_id.add continuous_const)).sub ha)
  have hInt : IntegrableOn (fun t : ℝ => frobSq (a (t + θ) - a t))
      (Set.Icc (0 : ℝ) (2 * Real.pi)) volume := hcont.integrableOn_Icc
  have heq (t : ℝ) :
      ENNReal.ofReal (frobSq (a (t + θ) - a t) / ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2) =
        angularKernel θ * ENNReal.ofReal (frobSq (a (t + θ) - a t)) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (frobSq_nonneg _)]
    exact mul_comm _ _
  simp_rw [heq]
  unfold angularKernel
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun t => frobSq_nonneg _)]
  rfl

theorem halfSobolevSq_le_of_angularDifference_le
    (a b : ℝ → Matrix (Fin r) (Fin r) ℂ) (ha : Continuous a) (hb : Continuous b)
    (C : ℝ) (hC : 0 ≤ C) (hab : ∀ θ, angularDifference a θ ≤ C * angularDifference b θ) :
    halfSobolevSq a ≤ ENNReal.ofReal C * halfSobolevSq b := by
  rw [halfSobolevSq_eq_lintegral_angularDifference a ha,
    halfSobolevSq_eq_lintegral_angularDifference b hb]
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2)⁻¹ *
        ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
          angularKernel θ * (ENNReal.ofReal C * ENNReal.ofReal (angularDifference b θ)) := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro θ
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (hab θ)
    _ = _ := by
      simp_rw [mul_left_comm (angularKernel _) (ENNReal.ofReal C),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      ac_rfl

end Yau.NodeProofs.D06Aux
