import Yau.Proofs.Y01InverseJets
import Yau.Proofs.Y01PolynomialJets

/-! The finite inverse-jet identity converts a model of the coordinate
transition into the original jet conjugacy. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem polyMap_eval_id : (PolyMap.id : PolyMap n).eval = id := by
  funext z
  ext i
  simp [PolyMap.eval, PolyMap.id]

theorem polyMap_eval_comp_fun (P Q : PolyMap n) : (P.comp Q).eval = P.eval ∘ Q.eval :=
  funext (polyMap_eval_comp P Q)

theorem jetComp_germJetEq (P Q : PolyMap n) (d : ℕ) :
    GermJetEq (jetComp d P Q).eval (P.eval ∘ Q.eval) d := by
  rw [← polyMap_eval_comp_fun]
  exact jetEq_germJetEq (jetComp_jetEq d P Q)

theorem germ_conjugacy_of_inverse
    {G H Hnext Hinv : PolyMap n} {F : ComplexVector n → ComplexVector n}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0)
    (hH : H.FixesZero) (hHinv : Hinv.FixesZero)
    (hinverse : PolyMap.JetEq (Hinv.comp H) PolyMap.id d)
    (hmodel : GermJetEq G.eval (Hnext.eval ∘ F ∘ Hinv.eval) d) :
    GermJetEq (Hnext.eval ∘ F) (G.eval ∘ H.eval) d := by
  have hH0 := (fixesZero_iff_eval_zero H).1 hH
  have hI0 := (fixesZero_iff_eval_zero Hinv).1 hHinv
  have hHsmooth : ContDiffAt ℂ d H.eval 0 :=
    ((polyMap_eval_contDiff H).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hIsmooth : ContDiffAt ℂ d Hinv.eval 0 :=
    ((polyMap_eval_contDiff Hinv).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hGsmooth : ContDiffAt ℂ d G.eval 0 :=
    ((polyMap_eval_contDiff G).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hNsmooth : ContDiffAt ℂ d Hnext.eval 0 :=
    ((polyMap_eval_contDiff Hnext).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hNAtF : ContDiffAt ℂ d Hnext.eval (F 0) := by simpa only [hF0] using hNsmooth
  have houter : ContDiffAt ℂ d (Hnext.eval ∘ F) 0 := hNAtF.comp 0 hF
  have hOuterAtI : ContDiffAt ℂ d (Hnext.eval ∘ F) (Hinv.eval 0) := by
    simpa only [hI0] using houter
  have htarget : ContDiffAt ℂ d (Hnext.eval ∘ F ∘ Hinv.eval) 0 := hOuterAtI.comp 0 hIsmooth
  have hpre := germJetEq_comp hHsmooth hHsmooth hGsmooth htarget hH0 hH0
    (germJetEq_refl H.eval d) hmodel
  have hinner : GermJetEq (Hinv.eval ∘ H.eval) id d := by
    rw [← polyMap_eval_comp_fun, ← polyMap_eval_id]
    exact jetEq_germJetEq hinverse
  have hIAtH : ContDiffAt ℂ d Hinv.eval (H.eval 0) := by simpa only [hH0] using hIsmooth
  have hinnerSmooth : ContDiffAt ℂ d (Hinv.eval ∘ H.eval) 0 := hIAtH.comp 0 hHsmooth
  have hinnerZero : (Hinv.eval ∘ H.eval) 0 = 0 := by
    simp only [Function.comp_apply, hH0, hI0]
  have hpost := germJetEq_comp hinnerSmooth contDiffAt_id houter houter hinnerZero rfl
    hinner (germJetEq_refl (Hnext.eval ∘ F) d)
  have htotal := germJetEq_trans hpre (by
    simpa only [Function.comp_assoc, Function.comp_id] using hpost)
  exact germJetEq_symm htotal

theorem all_forward_automorphisms {G Ginv : ℕ → PolyMap n}
    (hG : ∀ k, IsPolyAutomorphism (G k) (Ginv k)) :
    ∀ k, IsPolyAutomorphism (forwardComp G k) (backwardComp Ginv k) := by
  intro k
  induction k with
  | zero => exact automorphism_id
  | succ k ih => exact automorphism_comp (hG k) ih

end Yau.Proofs.Y01Aux
