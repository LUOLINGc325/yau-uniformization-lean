import Yau.Proofs.P06HodgeRegularityBoundedPairing
import Yau.Proofs.P06HodgeRegularityWordTranspose

/-! Uniqueness makes actual smooth representatives of a linear L² map
linear pointwise. Their actual bounded spatial jets are linear as well. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ν : Measure E) [ν.IsOpenPosMeasure]

theorem regularitySmoothLift_add
    (P : H →L[ℝ] Lp ℝ 2 ν) (R : H → E → ℝ)
    (hR : ∀ f, Continuous (R f)) (hRAE : ∀ f, R f =ᵐ[ν] (P f : E → ℝ)) (f g : H) :
    R (f+g) = fun z => R f z + R g z := by
  apply Measure.eq_of_ae_eq (μ := ν) _ (hR (f+g)) ((hR f).add (hR g))
  filter_upwards [hRAE (f+g),hRAE f,hRAE g,Lp.coeFn_add (P f) (P g)] with z hz hf hg hp
  rw [hz,map_add,hp]
  simp only [Pi.add_apply]
  rw [← hf,← hg]

theorem regularitySmoothLift_smul
    (P : H →L[ℝ] Lp ℝ 2 ν) (R : H → E → ℝ)
    (hR : ∀ f, Continuous (R f)) (hRAE : ∀ f, R f =ᵐ[ν] (P f : E → ℝ)) (a : ℝ) (f : H) :
    R (a • f) = fun z => a * R f z := by
  apply Measure.eq_of_ae_eq (μ := ν) _ (hR (a • f)) (continuous_const.mul (hR f))
  filter_upwards [hRAE (a • f),hRAE f,Lp.coeFn_smul a (P f)] with z hz hf hp
  rw [hz,map_smul,hp,Pi.smul_apply,smul_eq_mul,← hf]
  rfl

def regularitySmoothLiftJetLinear
    (P : H →L[ℝ] Lp ℝ 2 ν) (R : H → E → ℝ)
    (hR : ∀ f, ContDiff ℝ ∞ (R f)) (hcR : ∀ f, HasCompactSupport (R f))
    (hRAE : ∀ f, R f =ᵐ[ν] (P f : E → ℝ)) (v : ι → E) (w : List ι) : H →ₗ[ℝ] (E →ᵇ ℝ) where
  toFun f := ofCompactSupport (regularityCoefficientWord v w (R f))
    (regularityCoefficientWord_contDiff v (hR f) w).continuous
    (regularityCoefficientWord_regular v (hR f) (hcR f) w).2.1
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro z
    change regularityCoefficientWord v w (R (f+g)) z =
      regularityCoefficientWord v w (R f) z + regularityCoefficientWord v w (R g) z
    rw [regularitySmoothLift_add ν P R (fun f => (hR f).continuous) hRAE,
      regularityCoefficientWord_add v (hR f) (hR g)]
  map_smul' a f := by
    apply BoundedContinuousFunction.ext
    intro z
    change regularityCoefficientWord v w (R (a • f)) z = a * regularityCoefficientWord v w (R f) z
    rw [regularitySmoothLift_smul ν P R (fun f => (hR f).continuous) hRAE,
      regularityCoefficientWord_const_mul v (hR f)]

end Yau.NodeProofs.P06Aux
