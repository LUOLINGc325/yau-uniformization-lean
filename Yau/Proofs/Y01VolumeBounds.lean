import Yau.Proofs.Y01PolynomialBounds
import Yau.Proofs.Y01JetCompositionBounds
import Yau.Proofs.Y01CoordinateGerms

/-! Bounds for the actual Y05 transition polynomial follow from its germ
identity and finite coefficient extraction; no separate V bound is assumed. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem partitionJetConstant_nonneg (d : ℕ) : 0 ≤ partitionJetConstant d := by
  unfold partitionJetConstant
  positivity

theorem cauchyJetConstant_nonneg (d : ℕ) : 0 ≤ cauchyJetConstant d := by
  unfold cauchyJetConstant
  positivity

theorem jetNorm_comp_bound_of_bounds
    {f g : ComplexVector n → ComplexVector n} {A B : ℝ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0) (hf0 : f 0 = 0)
    (hA : jetNorm f d ≤ A) (hB : jetNorm g d ≤ B) :
    jetNorm (g ∘ f) d ≤ partitionJetConstant d * B * (1 + A) ^ d := by
  have hA0 : 0 ≤ A := (jetNorm_nonneg f d).trans hA
  have hB0 : 0 ≤ B := (jetNorm_nonneg g d).trans hB
  have hp := partitionJetConstant_nonneg d
  have hpow : (1 + jetNorm f d) ^ d ≤ (1 + A) ^ d :=
    pow_le_pow_left₀ (by linarith [jetNorm_nonneg f d]) (by linarith) d
  exact (jetNorm_comp_bound hf hg hf0).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hB hp) hpow (pow_nonneg (by linarith [jetNorm_nonneg f d]) d) (mul_nonneg hp hB0))

theorem volume_transition_coeffNorm_bound
    {Anext Ainv V : PolyMap n} {F : ComplexVector n → ComplexVector n} {B : ℝ}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0) (hAinv : Ainv.FixesZero)
    (hB : jetNorm F d ≤ B) (hVdegree : V.degree ≤ d)
    (hV : GermJetEq (Anext.eval ∘ F ∘ Ainv.eval) V.eval d) :
    V.coeffNorm ≤ ((n : ℝ) * ((boundedMonomials n d).card : ℝ)) *
      (partitionJetConstant d * (cauchyJetConstant d * Anext.coeffNorm) *
        (1 + partitionJetConstant d * B *
          (1 + cauchyJetConstant d * Ainv.coeffNorm) ^ d) ^ d) := by
  have hA0 := (fixesZero_iff_eval_zero _).1 hAinv
  have hFA : ContDiffAt ℂ d (F ∘ Ainv.eval) 0 :=
    contDiffAt_comp_zero (polyMap_contDiffAt Ainv) hF hA0
  have hFA0 : (F ∘ Ainv.eval) 0 = 0 := by simp only [Function.comp_apply, hA0, hF0]
  have hInner := jetNorm_comp_bound_of_bounds (polyMap_contDiffAt Ainv) hF hA0
    (jetNorm_eval_le_coeffNorm Ainv d) hB
  have hOuter := jetNorm_comp_bound_of_bounds hFA (polyMap_contDiffAt Anext) hFA0
    hInner (jetNorm_eval_le_coeffNorm Anext d)
  have heq := jetNorm_eq_of_germJetEq hV
  rw [heq] at hOuter
  exact (coeffNorm_le_jetNorm V hVdegree).trans
    (mul_le_mul_of_nonneg_left hOuter (by positivity))

end Yau.Proofs.Y01Aux
