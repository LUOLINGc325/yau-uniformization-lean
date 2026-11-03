import Yau.Proofs.Y06RegularLimit

/-! Replace a polynomial jet by the same actual smooth transition germ.
The corrections, inverses, constants, finite terminal identities and subsequence stay fixed. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y01Aux Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d Dstar : ℕ}

theorem regularJetSolution_transport
    {Fhat Fhat' : ℕ → ComplexVector n → ComplexVector n}
    {D J : ℕ → Herm n} {w : ℕ → Fin n → ℝ} {active : ℕ → Prop}
    {s : ℕ → ℝ} {C : ℝ} {Q : JetData n}
    (hdata : ∀ k, active k → ContDiffAt ℂ d (Fhat k) 0 ∧ ContDiffAt ℂ d (Fhat' k) 0 ∧
      Fhat k 0 = 0 ∧ Fhat' k 0 = 0 ∧ GermJetEq (Fhat k) (Fhat' k) d)
    (hsol : RegularJetSolution Fhat D J w active d Dstar s C Q) :
    RegularJetSolution Fhat' D J w active d Dstar s C Q := by
  refine ⟨hsol.1, ?_⟩
  intro k hk
  obtain ⟨hlin, hdeg, hvol, hIdeg, hI0, hleft, hright, hforb, hG0, hGlin, hGall,
    hAuto, hGdeg, hGIdeg, hGjac, hjet, hnorm⟩ := hsol.2 k hk
  obtain ⟨hf, hf', hf0, hf'0, hff'⟩ := hdata k hk
  let O := (linearPolynomial (J k)⁻¹).comp ((Q.correction (k + 1)).comp (linearPolynomial (J k)))
  have hO : ContDiffAt ℂ d O.eval 0 :=
    (polyMap_eval_contDiff O).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have houter : O.eval = fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k)⁻¹
      ((Q.correction (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) z)) := by
    funext z
    change ((linearPoly (J k)⁻¹).comp ((Q.correction (k + 1)).comp (linearPoly (J k)))).eval z = _
    rw [polyMap_eval_comp, polyMap_eval_comp, linearPoly_eval, linearPoly_eval]
  have hpost := germJetEq_comp hf hf' hO hO hf0 hf'0 hff' (germJetEq_refl O.eval d)
  have heq (f : ComplexVector n → ComplexVector n) : O.eval ∘ f =
      fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k)⁻¹
        ((Q.correction (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) (f z))) := by
    rw [houter]; rfl
  have hpost' := germJetEq_transport (heq (Fhat k)) (heq (Fhat' k)) hpost
  exact ⟨hlin, hdeg, hvol, hIdeg, hI0, hleft, hright, hforb, hG0, hGlin, hGall,
    hAuto, hGdeg, hGIdeg, hGjac, germJetEq_trans hjet hpost', hnorm⟩

theorem regularJetRuns_transport
    {Fhat Fhat' : ℕ → ComplexVector n → ComplexVector n}
    {D J : ℕ → Herm n} {w : ℕ → Fin n → ℝ} {reg : ℕ → Prop} {s : ℕ → ℝ}
    (hdata : ∀ k, reg k → ContDiffAt ℂ d (Fhat k) 0 ∧ ContDiffAt ℂ d (Fhat' k) 0 ∧
      Fhat k 0 = 0 ∧ Fhat' k 0 = 0 ∧ GermJetEq (Fhat k) (Fhat' k) d)
    (hruns : RegularJetRuns Fhat D J w reg d Dstar s) :
    RegularJetRuns Fhat' D J w reg d Dstar s := by
  obtain ⟨C, hC, hglobal, hfinite, htail⟩ := hruns
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := hglobal
    exact ⟨Q, regularJetSolution_transport hdata hQ⟩
  · intro a len hlen hreg
    obtain ⟨Q, hQ, hterminal⟩ := hfinite a len hlen hreg
    exact ⟨Q, regularJetSolution_transport (fun k hk => hdata k (hreg k hk.1 hk.2)) hQ, hterminal⟩
  · intro a hreg
    obtain ⟨Q, finite, σ, hσ, hQ, hfinite, hlim⟩ := htail a hreg
    refine ⟨Q, finite, σ, hσ, regularJetSolution_transport (fun k hk => hdata k (hreg k hk)) hQ, ?_, hlim⟩
    intro H
    exact ⟨regularJetSolution_transport (fun k hk => hdata k (hreg k hk.1)) (hfinite H).1, (hfinite H).2⟩

theorem polynomial_sandwich_smooth {Outer Inner : PolyMap n}
    {F : ComplexVector n → ComplexVector n}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0) (hInner : Inner.FixesZero) :
    ContDiffAt ℂ d (Outer.eval ∘ F ∘ Inner.eval) 0 := by
  have hI : ContDiffAt ℂ d Inner.eval 0 :=
    (polyMap_eval_contDiff Inner).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hIz := (fixesZero_iff_eval_zero _).mp hInner
  have hFI : ContDiffAt ℂ d F (Inner.eval 0) := by simpa only [hIz] using hF
  have hcomp : ContDiffAt ℂ d (F ∘ Inner.eval) 0 := hFI.comp 0 hI
  have hO : ContDiffAt ℂ d Outer.eval ((F ∘ Inner.eval) 0) :=
    (polyMap_eval_contDiff Outer).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  exact hO.comp 0 hcomp

end Yau.Proofs.Y06Aux
