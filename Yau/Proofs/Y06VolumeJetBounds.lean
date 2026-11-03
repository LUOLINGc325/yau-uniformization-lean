import Yau.Proofs.Y01PolynomialBounds
import Yau.Proofs.Y01JetCompositionBounds
import Yau.Proofs.Y06GermLinearization

/-! The original V coefficient bound is derived from its actual germ and
the original regular transition jet bound, at the same index. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux
open scoped ContDiff

variable {n d : ℕ}

theorem partitionConstant_nonneg (d : ℕ) : 0 ≤ partitionJetConstant d := by
  unfold partitionJetConstant
  positivity

theorem cauchyConstant_nonneg (d : ℕ) : 0 ≤ cauchyJetConstant d := by
  unfold cauchyJetConstant
  positivity

theorem jetNorm_comp_of_bounds
    {f g : ComplexVector n → ComplexVector n} {A B : ℝ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0) (hf0 : f 0 = 0)
    (hA : jetNorm f d ≤ A) (hB : jetNorm g d ≤ B) :
    jetNorm (g ∘ f) d ≤ partitionJetConstant d * B * (1 + A) ^ d := by
  have hA0 : 0 ≤ A := (jetNorm_nonneg f d).trans hA
  have hB0 : 0 ≤ B := (jetNorm_nonneg g d).trans hB
  have hp := partitionConstant_nonneg d
  have hpow : (1 + jetNorm f d) ^ d ≤ (1 + A) ^ d :=
    pow_le_pow_left₀ (by linarith [jetNorm_nonneg f d]) (by linarith) d
  exact (jetNorm_comp_bound hf hg hf0).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hB hp) hpow
      (pow_nonneg (by linarith [jetNorm_nonneg f d]) d) (mul_nonneg hp hB0))

theorem volume_transition_coefficient_bound
    {Outer Inner V : PolyMap n} {F : ComplexVector n → ComplexVector n} {B : ℝ}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0) (hInner0 : Inner.FixesZero)
    (hB : jetNorm F d ≤ B) (hVdegree : V.degree ≤ d)
    (hV : GermJetEq (Outer.eval ∘ F ∘ Inner.eval) V.eval d) :
    V.coeffNorm ≤ ((n : ℝ) * ((boundedMonomials n d).card : ℝ)) *
      (partitionJetConstant d * (cauchyJetConstant d * Outer.coeffNorm) *
        (1 + partitionJetConstant d * B * (1 + cauchyJetConstant d * Inner.coeffNorm) ^ d) ^ d) := by
  have hI0 := (fixesZero_iff_eval_zero _).mp hInner0
  have hI : ContDiffAt ℂ d Inner.eval 0 :=
    (polyMap_eval_contDiff _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hO : ContDiffAt ℂ d Outer.eval 0 :=
    (polyMap_eval_contDiff _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hFI : ContDiffAt ℂ d F (Inner.eval 0) := by simpa only [hI0] using hF
  have hFA : ContDiffAt ℂ d (F ∘ Inner.eval) 0 := hFI.comp 0 hI
  have hFA0 : (F ∘ Inner.eval) 0 = 0 := by simp only [Function.comp_apply, hI0, hF0]
  have hInner := jetNorm_comp_of_bounds hI hF hI0 (jetNorm_eval_le_coeffNorm Inner d) hB
  have hOuter := jetNorm_comp_of_bounds hFA hO hFA0 hInner (jetNorm_eval_le_coeffNorm Outer d)
  rw [jetNorm_eq_of_germJetEq hV] at hOuter
  exact (coeffNorm_le_jetNorm V hVdegree).trans
    (mul_le_mul_of_nonneg_left hOuter (by positivity))

end Yau.Proofs.Y06Aux
