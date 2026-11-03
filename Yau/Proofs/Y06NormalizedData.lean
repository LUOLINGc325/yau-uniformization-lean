import Yau.Proofs.Y06NormalizedJet
import Yau.Proofs.Y06RunTransport

/-! The original volume-normalized transition is the same smooth germ
as its polynomial jet, at every regular index. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux
open scoped ContDiff

variable {n d : ℕ}

theorem normalizedRegularTransition_data
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk s d r last logs B ell Evol A Ainv V) (hd : 1 ≤ d)
    (hF : ∀ k, F (tk k) (tk (k + 1)) 0 = 0 ∧
      DifferentiableOn ℂ (F (tk k) (tk (k + 1))) (Metric.ball 0 r))
    {L : Changes n} {w : ℕ → Fin n → ℝ} {j : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ}
    {reg : ℕ → Prop} (hL : ∀ k, reg k → ChangeAt (diagonal F tk E) w j S C c L k) :
    ∀ k, reg k → IsConstantVolumeJet (normalizedPolynomial V E L k) d ∧
      (normalizedPolynomial V E L k).linearPart = diagonal F tk E k ∧
      GermJetEq (normalizedPolynomial V E L k).eval (normalizedRegularTransition F tk A Ainv E L k) d ∧
      ContDiffAt ℂ d (normalizedRegularTransition F tk A Ainv E L k) 0 ∧
      normalizedRegularTransition F tk A Ainv E L k 0 = 0 := by
  intro k hk
  obtain ⟨hPCV, hPlin, hPjet⟩ := normalizedPolynomial_data hE hVol hd k (hF k).1 (hF k).2 (hL k hk)
  obtain ⟨_, _, _, _, _, _, _, _, hI0, _, _, _, _, _, _, _, _⟩ := hVol.2.2.2.1 k
  obtain ⟨_, _, _, _, _, _, _, hA0, _, _, _, _, _, _, _, _, _⟩ := hVol.2.2.2.1 (k + 1)
  let Rplus := L.plus k * (E.finish k).conjTranspose
  let Rminus := E.start k * (L.minus k)⁻¹
  let Outer := (linearPolynomial Rplus).comp (A (k + 1))
  let Inner := (Ainv k).comp (linearPolynomial Rminus)
  have hOuter0 : Outer.FixesZero := comp_fixesZero (linearPoly_fixesZero Rplus) hA0
  have hInner0 : Inner.FixesZero := comp_fixesZero hI0 (linearPoly_fixesZero Rminus)
  have hFsmooth : ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0 :=
    (holomorphic_ball_smooth hVol.1 (hF k).2).of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : Outer.eval ∘ F (tk k) (tk (k + 1)) ∘ Inner.eval =
      normalizedRegularTransition F tk A Ainv E L k := by
    funext z
    change ((linearPoly Rplus).comp (A (k + 1))).eval
      (F (tk k) (tk (k + 1)) (((Ainv k).comp (linearPoly Rminus)).eval z)) = _
    rw [polyMap_eval_comp, polyMap_eval_comp, linearPoly_eval, linearPoly_eval]
    rfl
  have hsmooth := polynomial_sandwich_smooth (Outer := Outer) hFsmooth (hF k).1 hInner0
  rw [heq] at hsmooth
  have hzero : normalizedRegularTransition F tk A Ainv E L k 0 = 0 := by
    rw [← heq]
    simp only [Function.comp_apply, (fixesZero_iff_eval_zero _).mp hInner0,
      (hF k).1, (fixesZero_iff_eval_zero _).mp hOuter0]
  exact ⟨hPCV, hPlin, hPjet, hsmooth, hzero⟩

end Yau.Proofs.Y06Aux
