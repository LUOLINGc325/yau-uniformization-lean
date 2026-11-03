import Yau.Proofs.Y06JetDataLimits
import Yau.Proofs.Y06PolynomialLimits
import Yau.Proofs.Y06PolynomialGerms
import Yau.Proofs.Y06FiniteStages
import Yau.Proofs.Y06GermLinearization

/-! Every clause of the original regular jet solution is closed under one
common coefficient subsequence. The jet identity is passed as a polynomial identity. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open Yau.Proofs.Y01Aux
open scoped Topology

variable {n d Dstar : ℕ}

theorem layerRight_eval_fun (P H : ℕ → PolyMap n) (J : ℕ → Herm n) (k : ℕ) :
    (layerRight P H J k).eval = fun z =>
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k)⁻¹
        ((H (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) ((P k).eval z))) := by
  funext z
  change ((linearPoly (J k)⁻¹).comp ((H (k + 1)).comp ((linearPoly (J k)).comp (P k)))).eval z = _
  rw [polyMap_eval_comp, polyMap_eval_comp, polyMap_eval_comp, linearPoly_eval, linearPoly_eval]

theorem regular_polynomial_jet_identity {P : ℕ → PolyMap n} {J : ℕ → Herm n}
    {Q : JetData n} {k : ℕ}
    (h : GermJetEq (fun z => (Q.model k).eval ((Q.correction k).eval z))
      (fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k)⁻¹
        ((Q.correction (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) ((P k).eval z)))) d) :
    PolyMap.JetEq ((Q.model k).comp (Q.correction k)) (layerRight P Q.correction J k) d := by
  have hleft : ((Q.model k).comp (Q.correction k)).eval =
      fun z => (Q.model k).eval ((Q.correction k).eval z) := funext (polyMap_eval_comp _ _)
  exact germJetEq_polynomial_jetEq (germJetEq_transport hleft.symm (layerRight_eval_fun P Q.correction J k).symm h)

theorem regularJetSolution_polynomial_limit
    (P : ℕ → PolyMap n) (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ)
    (activeH : ℕ → ℕ → Prop) (active : ℕ → Prop) (s : ℕ → ℝ) (C : ℝ)
    (Q : ℕ → JetData n) (R : JetData n) (Dbound : ℕ)
    (hdegree : ∀ H, JetDataDegreeBound Dbound (Q H)) (hRdegree : JetDataDegreeBound Dbound R)
    (hlim : JetDataCoefficientTendsto Q R)
    (hactive : ∀ k, ∀ᶠ H in atTop, activeH H k ↔ active k)
    (hsol : ∀ H, RegularJetSolution (fun k => (P k).eval) D J w (activeH H) d Dstar s C (Q H)) :
    RegularJetSolution (fun k => (P k).eval) D J w active d Dstar s C R := by
  have hH (k i) : CoefficientTendsto (fun H => (Q H).correction k i) (R.correction k i) := fun β => (hlim k i β).1
  have hI (k i) : CoefficientTendsto (fun H => (Q H).inverseJet k i) (R.inverseJet k i) := fun β => (hlim k i β).2.1
  have hG (k i) : CoefficientTendsto (fun H => (Q H).model k i) (R.model k i) := fun β => (hlim k i β).2.2.1
  have hGI (k i) : CoefficientTendsto (fun H => (Q H).inverseModel k i) (R.inverseModel k i) := fun β => (hlim k i β).2.2.2
  have hId (i : Fin n) := coefficientTendsto_const ((PolyMap.id : PolyMap n) i)
  refine ⟨?_, ?_⟩
  · intro k hk
    have hnot : ∀ᶠ H in atTop, ¬activeH H k := (hactive k).mono (fun H h => fun ha => hk (h.mp ha))
    constructor
    · funext i
      exact coefficientTendsto_unique (hH k i) (hId i)
        (hnot.mono (fun H h => congrFun ((hsol H).1 k h).1 i))
    · funext i
      exact coefficientTendsto_unique (hI k i) (hId i)
        (hnot.mono (fun H h => congrFun ((hsol H).1 k h).2 i))
  · intro k hk
    have hact : ∀ᶠ H in atTop, activeH H k := (hactive k).mono (fun H h => h.mpr hk)
    have hall := hact.mono (fun H h => (hsol H).2 k h)
    simp only [Filter.eventually_and] at hall
    obtain ⟨hlin, hdeg, hvol, hIdeg, hI0, hleft, hright, hforb, hG0, hGlin, hGall,
      hAuto, hGdeg, hGIdeg, hGjac, hjet, hnorm⟩ := hall
    have hRlin := coefficientTendsto_linearPart (hH k) hlin
    have hRHdeg := coefficientTendsto_degree (hH k) hdeg
    have hRIdeg := coefficientTendsto_degree (hI k) hIdeg
    have hRH0 := coefficientTendsto_fixesZero (hH k) (hvol.mono (fun H h => h.1))
    have hRI0 := coefficientTendsto_fixesZero (hI k) hI0
    have hRG0 := coefficientTendsto_fixesZero (hG k) hG0
    have hRGlin := coefficientTendsto_linearPart (hG k) hGlin
    have hRGdeg := coefficientTendsto_degree (hG k) hGdeg
    have hRGIdeg := coefficientTendsto_degree (hGI k) hGIdeg
    have hHI := coefficientTendsto_comp_bounded (hH k) (hI k)
      (fun H => (hdegree H k).1) (hRdegree k).1
    have hIH := coefficientTendsto_comp_bounded (hI k) (hH k)
      (fun H => (hdegree H k).2.1) (hRdegree k).2.1
    have hGGI := coefficientTendsto_comp_bounded (hG k) (hGI k)
      (fun H => (hdegree H k).2.2.1) (hRdegree k).2.2.1
    have hGIG := coefficientTendsto_comp_bounded (hGI k) (hG k)
      (fun H => (hdegree H k).2.2.2) (hRdegree k).2.2.2
    have hRauto : IsPolyAutomorphism (R.model k) (R.inverseModel k) := by
      constructor
      · funext i
        exact coefficientTendsto_unique (hGGI i) (hId i) (hAuto.mono (fun H h => congrFun h.1 i))
      · funext i
        exact coefficientTendsto_unique (hGIG i) (hId i) (hAuto.mono (fun H h => congrFun h.2 i))
    have hGH := coefficientTendsto_comp_bounded (hG k) (hH k)
      (fun H => (hdegree H k).2.2.1) (hRdegree k).2.2.1
    have hNext := coefficientTendsto_comp_bounded (hH (k + 1))
      (fun i => coefficientTendsto_const (((linearPolynomial (J k)).comp (P k)) i))
      (fun H => (hdegree H (k + 1)).1) (hRdegree (k + 1)).1
    have hRight := coefficientTendsto_comp_bounded
      (fun i => coefficientTendsto_const (linearPolynomial (J k)⁻¹ i)) hNext
      (fun _ => linearPoly_degree_le (J k)⁻¹) (linearPoly_degree_le (J k)⁻¹)
    have hRjet : PolyMap.JetEq ((R.model k).comp (R.correction k))
        (layerRight P R.correction J k) d :=
      coefficientTendsto_jetEq hGH hRight (hjet.mono (fun H h => regular_polynomial_jet_identity h))
    have hRjetGerm : GermJetEq (fun z => (R.model k).eval ((R.correction k).eval z))
        (fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k)⁻¹
          ((R.correction (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) ((P k).eval z)))) d :=
      germJetEq_transport (funext (polyMap_eval_comp _ _)) (layerRight_eval_fun _ _ _ _) (jetEq_germJetEq hRjet)
    have hnormH := coeffNorm_tendsto_of_bounded_degree (hH k) (fun H => (hdegree H k).1) (hRdegree k).1
    have hnormI := coeffNorm_tendsto_of_bounded_degree (hI k) (fun H => (hdegree H k).2.1) (hRdegree k).2.1
    have hnormG := coeffNorm_tendsto_of_bounded_degree (hG k) (fun H => (hdegree H k).2.2.1) (hRdegree k).2.2.1
    have hnormGI := coeffNorm_tendsto_of_bounded_degree (hGI k) (fun H => (hdegree H k).2.2.2) (hRdegree k).2.2.2
    refine ⟨hRlin, hRHdeg, ⟨hRH0, hRHdeg, ?_, ?_⟩, hRIdeg, hRI0, ?_, ?_, ?_,
      hRG0, hRGlin, ?_, hRauto, hRGdeg, hRGIdeg, ?_, hRjetGerm, ?_⟩
    · rw [hRlin, Matrix.det_one]; exact one_ne_zero
    · exact coefficientTendsto_positiveJacFlat (hH k) (hvol.mono (fun H h => h.2.2.2))
    · exact coefficientTendsto_jetEq hHI hId hleft
    · exact coefficientTendsto_jetEq hIH hId hright
    · exact coefficientTendsto_onlyForbidden (hH k) hforb
    · exact coefficientTendsto_allowed (hG k) hGall
    · exact coefficientTendsto_unique (coefficientTendsto_jacDet (hG k)) (coefficientTendsto_const _) hGjac
    · exact le_of_tendsto (((hnormH.add hnormI).add hnormG).add hnormGI) hnorm

end Yau.Proofs.Y06Aux
