import Yau.Proofs.Y01LinearEvaluation
import Yau.Proofs.Y01GermComposition
import Yau.Proofs.Y03Frames
import Yau.LeafProofs.L17HolomorphicRegularity

/-! Finite derivatives of the same original holomorphic transition, and
linear transport of its germ jet. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux
open scoped ContDiff

variable {n d : ℕ}

theorem holomorphic_ball_smooth {m : ℕ} {f : ComplexVector n → ComplexVector m} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (Metric.ball 0 r)) : ContDiffAt ℂ ∞ f 0 :=
  (Yau.LeafProofs.L17Holomorphic.complexVector_contDiffOn Metric.isOpen_ball hf).contDiffAt
    (Metric.ball_mem_nhds 0 hr)

theorem germJetEq_fderiv {f g : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (h : GermJetEq f g d) : fderiv ℂ f 0 = fderiv ℂ g 0 := by
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg (fun p => p (fun _ : Fin 1 => z)) (h 1 hd)
  simpa only [iteratedFDeriv_one_apply] using hz

theorem matrix_clm_ring_coe (A : Herm n) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toRingEquiv A =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A := rfl

set_option backward.isDefEq.respectTransparency false in
theorem polynomial_sandwich_linearPart
    {P Outer Inner : PolyMap n} {F : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (hF : DifferentiableAt ℂ F 0) (hF0 : F 0 = 0)
    (hI : Inner.FixesZero)
    (hjet : GermJetEq P.eval (Outer.eval ∘ F ∘ Inner.eval) d) :
    P.linearPart = Outer.linearPart * derivativeMatrix F * Inner.linearPart := by
  have hI0 := (fixesZero_iff_eval_zero _).mp hI
  have hN : DifferentiableAt ℂ Outer.eval (F 0) :=
    (polyMap_eval_contDiff Outer).differentiable (by simp) _
  have hOuter : DifferentiableAt ℂ (Outer.eval ∘ F) 0 := hN.comp 0 hF
  have hOuterI : DifferentiableAt ℂ (Outer.eval ∘ F) (Inner.eval 0) := by
    simpa only [hI0] using hOuter
  have hId : DifferentiableAt ℂ Inner.eval 0 :=
    (polyMap_eval_contDiff Inner).differentiable (by simp) _
  have h := germJetEq_fderiv hd hjet
  change fderiv ℂ P.eval 0 = fderiv ℂ ((Outer.eval ∘ F) ∘ Inner.eval) 0 at h
  rw [fderiv_comp 0 hOuterI hId, hI0, fderiv_comp 0 hN hF, hF0,
    fderiv_polyMap_eval, fderiv_polyMap_eval, fderiv_polyMap_eval] at h
  have hD : fderiv ℂ F 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (derivativeMatrix F) := by
    simpa only [centerDeriv] using (derivativeMatrix_toEuclideanCLM F).symm
  rw [hD] at h
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective
  simp only [map_mul]
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg (fun L => L z) h
  simpa only [matrix_clm_ring_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply] using hz

theorem germJetEq_transport {f g f' g' : ComplexVector n → ComplexVector n}
    (hf : f = f') (hg : g = g') (h : GermJetEq f g d) : GermJetEq f' g' d := by
  cases hf
  cases hg
  exact h

theorem germJetEq_linear_sandwich (A B : ComplexVector n →L[ℂ] ComplexVector n)
    {f g : ComplexVector n → ComplexVector n}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hfg : GermJetEq f g d) :
    GermJetEq (fun z => A (f (B z))) (fun z => A (g (B z))) d := by
  have hB : ContDiffAt ℂ d B 0 := B.contDiff.contDiffAt
  have hA : ContDiffAt ℂ d A 0 := A.contDiff.contDiffAt
  have hpre := germJetEq_comp hB hB hf hg (map_zero B) (map_zero B)
    (germJetEq_refl B d) hfg
  have hfB : ContDiffAt ℂ d f (B 0) := by simpa only [map_zero] using hf
  have hgB : ContDiffAt ℂ d g (B 0) := by simpa only [map_zero] using hg
  have hFB : ContDiffAt ℂ d (f ∘ B) 0 := hfB.comp 0 hB
  have hGB : ContDiffAt ℂ d (g ∘ B) 0 := hgB.comp 0 hB
  have hFB0 : (f ∘ B) 0 = 0 := by simp only [Function.comp_apply, map_zero, hf0]
  have hGB0 : (g ∘ B) 0 = 0 := by simp only [Function.comp_apply, map_zero, hg0]
  exact germJetEq_comp hFB hGB hA hA hFB0 hGB0 hpre (germJetEq_refl A d)

end Yau.Proofs.Y06Aux
