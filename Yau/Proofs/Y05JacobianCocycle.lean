import Yau.Proofs.Y05PolynomialJacobian
import Yau.Proofs.Y05DeterminantJets
import Yau.Proofs.Y05JetOperations
import Yau.Proofs.Y01PolynomialComposition

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Yau.Proofs.Y02Aux MvPolynomial Filter
open scoped ContDiff Topology

variable {n d : ℕ}

theorem scalarEval_bind (Q : PolyMap n) (p : MvPolynomial (Fin n) ℂ) :
    scalarEval (bind₁ Q p) = fun z => scalarEval p (Q.eval z) := by
  funext z
  exact eval₂Hom_bind₁ (RingHom.id ℂ) (fun i => z i) Q p

/-- The sign in the scalar cocycle gives the exact unnormalized Jacobian
identity in the finite coefficient filtration. -/
theorem jacobian_scalar_cocycle_order
    (hd : 1 ≤ d) {F : ComplexVector n → ComplexVector n} {P : ComplexVector n → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0) (hP : AnalyticAt ℂ P 0)
    {c : ℂ} (hc : c ≠ 0)
    (hlog : ∀ᶠ z in 𝓝 0, Complex.exp (P z) =
      LinearMap.det (fderiv ℂ F z).toLinearMap / c)
    {L₀ L₁ E₀ E₁ : MvPolynomial (Fin n) ℂ} {Q : PolyMap n}
    (hQ0 : Q.FixesZero) (hQF : GermJetEq Q.eval F d)
    (hCocycle : ScalarJetEq (scalarEval L₀)
      (fun z => P z + scalarEval L₁ (F z)) (d - 1))
    (hE₀ : ScalarJetEq (scalarEval E₀) (fun z => Complex.exp (scalarEval L₀ z)) (d - 1))
    (hE₁ : ScalarJetEq (scalarEval E₁) (fun z => Complex.exp (scalarEval L₁ z)) (d - 1)) :
    scalarOrderAtLeast d (bind₁ Q E₁ * Q.jacDet - C c * E₀) := by
  have hpoly (p : MvPolynomial (Fin n) ℂ) : ContDiff ℂ (d - 1 : ℕ) (scalarEval p) :=
    (Yau.Proofs.Y01Aux.polyEval_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top)
  have hpolyV : ContDiff ℂ (d - 1 : ℕ) Q.eval :=
    (Yau.Proofs.Y01Aux.polyMap_eval_contDiff Q).of_le (WithTop.coe_le_coe.mpr le_top)
  have hExp : ContDiff ℂ (d - 1 : ℕ) Complex.exp :=
    Complex.contDiff_exp.of_le (WithTop.coe_le_coe.mpr le_top)
  have hQzero : Q.eval 0 = 0 := (Yau.Proofs.Y01Aux.fixesZero_iff_eval_zero Q).mp hQ0
  have hFdiff : ContDiffAt ℂ (d - 1 : ℕ) F 0 := hF.contDiffAt
  have hL₁F : ContDiffAt ℂ (d - 1 : ℕ) (fun z => scalarEval L₁ (F z)) 0 :=
    (hpoly L₁).contDiffAt.comp 0 hFdiff
  have hRhs : ContDiffAt ℂ (d - 1 : ℕ) (fun z => P z + scalarEval L₁ (F z)) 0 :=
    hP.contDiffAt.add hL₁F
  have hPre : ScalarJetEq (fun z => scalarEval E₁ (Q.eval z))
      (fun z => Complex.exp (scalarEval L₁ (F z))) (d - 1) := by
    exact iteratedFDeriv_comp_congr_through hpolyV.contDiffAt hFdiff
      (hpoly E₁).contDiffAt (hExp.comp (hpoly L₁)).contDiffAt hQzero hF0
      (fun m hm => hQF m (by omega)) hE₁
  have hDetGerm : (fun z => LinearMap.det (fderiv ℂ F z).toLinearMap) =ᶠ[𝓝 0]
      (fun z => c * Complex.exp (P z)) := by
    filter_upwards [hlog] with z hz
    have H := (div_eq_iff hc).mp hz.symm
    exact H.trans (mul_comm _ _)
  have hDetJet : ScalarJetEq (scalarEval Q.jacDet) (fun z => c * Complex.exp (P z))
      (d - 1) := by
    have hJ := germJetEq_jacobian_det hd
      ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff Q).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffAt hF.contDiffAt hQF
    have hFun : (fun z => LinearMap.det (fderiv ℂ Q.eval z).toLinearMap) =
        scalarEval Q.jacDet := funext (fun z => (scalarEval_jacDet Q z).symm)
    intro m hm
    have H : iteratedFDeriv ℂ m (scalarEval Q.jacDet) 0 =
        iteratedFDeriv ℂ m (fun z => LinearMap.det (fderiv ℂ F z).toLinearMap) 0 := by
      simpa only [hFun] using hJ m hm
    exact H.trans (hDetGerm.iteratedFDeriv ℂ m).eq_of_nhds
  have hProd := scalarJetEq_mul ((hpoly E₁).comp hpolyV).contDiffAt
    (hExp.contDiffAt.comp 0 hL₁F) (hpoly Q.jacDet).contDiffAt
    (contDiffAt_const.mul (hExp.contDiffAt.comp 0 hP.contDiffAt)) hPre hDetJet
  have hFunL : scalarEval (bind₁ Q E₁ * Q.jacDet) =
      fun z => scalarEval E₁ (Q.eval z) * scalarEval Q.jacDet z := by
    funext z
    simp only [scalarEval, map_mul]
    congr 1
    exact congrFun (scalarEval_bind Q E₁) z
  have hFunR : (fun z => Complex.exp (scalarEval L₁ (F z)) * (c * Complex.exp (P z))) =
      fun z => c * Complex.exp (P z + scalarEval L₁ (F z)) := by
    funext z
    rw [Complex.exp_add]
    ring
  have hProd' : ScalarJetEq (scalarEval (bind₁ Q E₁ * Q.jacDet))
      (fun z => c * Complex.exp (P z + scalarEval L₁ (F z))) (d - 1) := by
    change ScalarJetEq (fun z => scalarEval E₁ (Q.eval z) * scalarEval Q.jacDet z)
      (fun z => Complex.exp (scalarEval L₁ (F z)) * (c * Complex.exp (P z))) (d - 1) at hProd
    rw [hFunR] at hProd
    simpa only [hFunL] using hProd
  have hExpCocycle := scalarJetEq_exp (hpoly L₀).contDiffAt hRhs hCocycle
  have hExpE : ScalarJetEq (fun z => Complex.exp (P z + scalarEval L₁ (F z)))
      (scalarEval E₀) (d - 1) :=
    scalarJetEq_trans (scalarJetEq_symm hExpCocycle) (scalarJetEq_symm hE₀)
  have hScale := scalarJetEq_mul (contDiffAt_const : ContDiffAt ℂ (d - 1 : ℕ)
      (fun _ : ComplexVector n => c) 0) contDiffAt_const
    (hExp.contDiffAt.comp 0 hRhs) (hpoly E₀).contDiffAt (fun _ _ => rfl) hExpE
  have hFunC : scalarEval (C c * E₀) = fun z => c * scalarEval E₀ z := by
    funext z; simp [scalarEval]
  have hFinal : ScalarJetEq (scalarEval (bind₁ Q E₁ * Q.jacDet))
      (scalarEval (C c * E₀)) (d - 1) := by
    simpa only [hFunC] using scalarJetEq_trans hProd' hScale
  intro a ha
  change (bind₁ Q E₁ * Q.jacDet).coeff a - (C c * E₀).coeff a = 0
  exact sub_eq_zero.mpr (scalarJetEq_coefficients hFinal a (by omega))

end Yau.Proofs.Y05Aux
