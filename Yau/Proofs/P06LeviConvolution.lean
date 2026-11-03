import Yau.Proofs.P06LeviTests
import Yau.Proofs.P06FormDomain
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem convolution_direction_function {n : ℕ} (ρ f : ComplexVector n → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hf : Integrable f volume)
    (v : ComplexVector n) :
    (fun z => fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, volume] f) z v) =
      ((fun z => fderiv ℝ ρ z v) ⋆[lsmul ℝ ℝ, volume] f) := by
  funext z
  rw [convolution_directional_derivative volume ρ f (hρ.of_le (by simp)) hcρ hf z v,
    convolution_lsmul_swap]
  rfl

theorem convolution_directionSecond {n : ℕ} (ρ f : ComplexVector n → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hf : Integrable f volume)
    (z v : ComplexVector n) :
    directionSecond (ρ ⋆[lsmul ℝ ℝ, volume] f) v z =
      ∫ y, directionSecond ρ v (z - y) * f y := by
  have hDρ : ContDiff ℝ ∞ (fun a => fderiv ℝ ρ a v) :=
    (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [directionSecond, convolution_direction_function ρ f hρ hcρ hf v]
  exact convolution_directional_derivative volume _ f (hDρ.of_le (by simp))
    (hcρ.fderiv_apply ℝ v) hf z v

/-- The genuine Levi Hessian of a mollified rough L¹ input is the
integral of the actual constant-direction kernel Hessian. -/
theorem convolution_leviDirection {n : ℕ} (ρ f : ComplexVector n → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hf : Integrable f volume)
    (z v : ComplexVector n) :
    leviDirection (leviC (ρ ⋆[lsmul ℝ ℝ, volume] f) z) v =
      ∫ y, leviDirection (leviC ρ (z - y)) v * f y := by
  have hs : ContDiff ℝ ∞ (ρ ⋆[lsmul ℝ ℝ, volume] f) :=
    hcρ.contDiff_convolution_left (lsmul ℝ ℝ) hρ hf.locallyIntegrable
  have hi (w : ComplexVector n) : Integrable (fun y => directionSecond ρ w (z - y) * f y) volume := by
    have hd : ContDiff ℝ ∞ (fun a => fderiv ℝ ρ a w) :=
      (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdd : Continuous (directionSecond ρ w) :=
      ((hd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
    simpa only [lsmul_apply, smul_eq_mul, directionSecond] using
      (((hcρ.fderiv_apply ℝ w).fderiv_apply ℝ w).convolutionExists_left
        (lsmul ℝ ℝ) hdd hf.locallyIntegrable z).integrable_swap
  rw [leviDirection_eq_second (hs.contDiffAt.of_le (by simp)) v,
    convolution_directionSecond ρ f hρ hcρ hf z v,
    convolution_directionSecond ρ f hρ hcρ hf z (Complex.I • v)]
  have heq : (fun y => leviDirection (leviC ρ (z - y)) v * f y) =
      (fun y => (directionSecond ρ v (z - y) * f y +
        directionSecond ρ (Complex.I • v) (z - y) * f y) / 4) := by
    funext y
    rw [leviDirection_eq_second (hρ.contDiffAt.of_le (by simp)) v]
    ring
  rw [heq, integral_div, integral_add (hi v) (hi (Complex.I • v))]

theorem direction_reflect {n : ℕ} (ρ : ComplexVector n → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (z v : ComplexVector n) :
    (fun y => fderiv ℝ (fun a => ρ (z - a)) y v) =
      (fun y => -fderiv ℝ ρ (z - y) v) := by
  funext y
  have h := ((hρ.differentiable (by simp) (z - y)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).const_sub z)).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.id_apply, map_neg] using DFunLike.congr_fun h v

theorem directionSecond_reflect {n : ℕ} (ρ : ComplexVector n → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (z v y : ComplexVector n) :
    directionSecond (fun a => ρ (z - a)) v y = directionSecond ρ v (z - y) := by
  have hd : ContDiff ℝ ∞ (fun a => fderiv ℝ ρ a v) :=
    (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [directionSecond, direction_reflect ρ hρ z v]
  have heq : (fun a => -fderiv ℝ ρ (z - a) v) =
      -(fun a => (fun b => fderiv ℝ ρ b v) (z - a)) := rfl
  rw [heq, fderiv_neg]
  have h := congrFun (direction_reflect (fun a => fderiv ℝ ρ a v) hd z v) y
  simpa only [neg_apply, neg_neg, directionSecond] using congrArg Neg.neg h

theorem leviDirection_reflect {n : ℕ} (ρ : ComplexVector n → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (z v y : ComplexVector n) :
    leviDirection (leviC (fun a => ρ (z - a)) y) v = leviDirection (leviC ρ (z - y)) v := by
  have hRef : ContDiff ℝ ∞ (fun a => ρ (z - a)) := hρ.comp (contDiff_const.sub contDiff_id)
  rw [leviDirection_eq_second (hRef.contDiffAt.of_le (by simp)) v,
    leviDirection_eq_second (hρ.contDiffAt.of_le (by simp)) v,
    directionSecond_reflect ρ hρ z v y, directionSecond_reflect ρ hρ z (Complex.I • v) y]

end Yau.NodeProofs.P06Aux
