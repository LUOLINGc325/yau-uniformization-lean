import Yau.Proofs.Y05JacobianCocycle
import Yau.Proofs.Y05ConstantVolumeTaylor
import Yau.Proofs.Y05CompositionEstimates

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Yau.Proofs.Y02Aux MvPolynomial
open scoped ContDiff Topology

variable {n d : ℕ}

theorem normalized_jacobian_order
    {A₀ A₁ Q I : PolyMap n} {E₀ E₁ : MvPolynomial (Fin n) ℂ} {c : ℂ}
    (hA₀ : A₀.jacDet = E₀) (hA₁ : A₁.jacDet = E₁) (hI : I.FixesZero)
    (hinverse : PolyMap.JetEq (A₀.comp I) PolyMap.id d)
    (hscalar : scalarOrderAtLeast d (bind₁ Q E₁ * Q.jacDet - C c * E₀)) :
    scalarOrderAtLeast d (((A₁.comp Q).comp I).jacDet - C c) := by
  have hInv := Yau.Proofs.Y01Aux.jacDet_order_of_jetEq hinverse
  rw [jacDet_comp, hA₀, jacDet_id] at hInv
  have hBind := Yau.Proofs.Y01Aux.scalarOrderAtLeast_bind hscalar hI
  have hFirst := scalarOrderAtLeast_mul_right hBind I.jacDet
  have hSecond := scalarOrderAtLeast_mul_left (C c) hInv
  have H := scalarOrderAtLeast_add hFirst hSecond
  have heq : (bind₁ I (bind₁ Q E₁ * Q.jacDet - C c * E₀)) * I.jacDet +
      C c * (bind₁ I E₀ * I.jacDet - 1) =
        ((A₁.comp Q).comp I).jacDet - C c := by
    rw [jacDet_comp, jacDet_comp, hA₁]
    simp only [map_sub, map_mul, bind₁_C_right]
    ring
  rw [heq] at H
  exact H

theorem polynomial_eval_analyticAt (P : PolyMap n) (z : ComplexVector n) :
    AnalyticAt ℂ P.eval z :=
  U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty isOpen_univ
    (Yau.Proofs.Y01Aux.polyMap_eval_contDiff P).contDiffOn z (Set.mem_univ _)

theorem normalized_polynomial_germ
    {F : ComplexVector n → ComplexVector n} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    {A Q I : PolyMap n} (hQ0 : Q.FixesZero) (hI0 : I.FixesZero)
    (hQF : GermJetEq Q.eval F d) :
    GermJetEq ((A.comp Q).comp I).eval (fun z => A.eval (F (I.eval z))) d := by
  have hIs : ContDiffAt ℂ d I.eval 0 :=
    ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff I).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hQs : ContDiffAt ℂ d Q.eval 0 :=
    ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff Q).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hAs : ContDiffAt ℂ d A.eval 0 :=
    ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff A).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hIz : I.eval 0 = 0 := (Yau.Proofs.Y01Aux.fixesZero_iff_eval_zero I).mp hI0
  have hQz : Q.eval 0 = 0 := (Yau.Proofs.Y01Aux.fixesZero_iff_eval_zero Q).mp hQ0
  have hPre := Yau.Proofs.Y01Aux.germJetEq_comp hIs hIs hQs hF.contDiffAt hIz hIz
    (fun _ _ => rfl) hQF
  have hQI0 : (Q.eval ∘ I.eval) 0 = 0 := by simp only [Function.comp_apply, hIz, hQz]
  have hFI0 : (F ∘ I.eval) 0 = 0 := by simp only [Function.comp_apply, hIz, hF0]
  have hQIs : ContDiffAt ℂ d (Q.eval ∘ I.eval) 0 := by
    have hQs' : ContDiffAt ℂ d Q.eval (I.eval 0) := by simpa only [hIz] using hQs
    exact hQs'.comp 0 hIs
  have hFIs : ContDiffAt ℂ d (F ∘ I.eval) 0 := by
    have hFs : ContDiffAt ℂ d F (I.eval 0) := by simpa only [hIz] using hF.contDiffAt (n := (d : ℕ∞ω))
    exact hFs.comp 0 hIs
  have hPost := Yau.Proofs.Y01Aux.germJetEq_comp hQIs hFIs hAs hAs
    hQI0 hFI0 hPre (fun _ _ => rfl)
  have hpoly : ((A.comp Q).comp I).eval = A.eval ∘ (Q.eval ∘ I.eval) := by
    funext z
    simp only [Yau.Proofs.Y01Aux.polyMap_eval_comp, Function.comp_apply]
  simpa only [hpoly, Function.comp_def] using hPost

/-- The actual normalized germ has a genuine constant-volume polynomial
model once the coherent scalar cocycle and the finite inverse are constructed. -/
theorem exists_normalized_volume_model
    (hd : 1 ≤ d) {F : ComplexVector n → ComplexVector n} {P : ComplexVector n → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0) (hP : AnalyticAt ℂ P 0)
    {c : ℂ} (hc : c ≠ 0)
    (hlog : ∀ᶠ z in 𝓝 0, Complex.exp (P z) = LinearMap.det (fderiv ℂ F z).toLinearMap / c)
    {L₀ L₁ E₀ E₁ : MvPolynomial (Fin n) ℂ} {A₀ A₁ I : PolyMap n}
    (hA₀ : A₀.jacDet = E₀) (hA₁ : A₁.jacDet = E₁)
    (hA₁0 : A₁.FixesZero) (hI0 : I.FixesZero)
    (hinverse : PolyMap.JetEq (A₀.comp I) PolyMap.id d)
    (hCocycle : ScalarJetEq (scalarEval L₀) (fun z => P z + scalarEval L₁ (F z)) (d - 1))
    (hE₀ : ScalarJetEq (scalarEval E₀) (fun z => Complex.exp (scalarEval L₀ z)) (d - 1))
    (hE₁ : ScalarJetEq (scalarEval E₁) (fun z => Complex.exp (scalarEval L₁ z)) (d - 1)) :
    ∃ V : PolyMap n, V.degree ≤ d ∧ IsConstantVolumeJet V d ∧
      GermJetEq (fun z => A₁.eval (F (I.eval z))) V.eval d := by
  obtain ⟨Q, hQdeg, hQF, hQzero⟩ := exists_vector_taylor hF d
  have hQ0 := hQzero hF0
  have hscalar := jacobian_scalar_cocycle_order hd hF hF0 hP hc hlog hQ0 hQF hCocycle hE₀ hE₁
  let S : PolyMap n := (A₁.comp Q).comp I
  have hOrder : scalarOrderAtLeast d (S.jacDet - C c) :=
    normalized_jacobian_order hA₀ hA₁ hI0 hinverse hscalar
  let G : ComplexVector n → ComplexVector n := fun z => A₁.eval (F (I.eval z))
  have hIz : I.eval 0 = 0 := (Yau.Proofs.Y01Aux.fixesZero_iff_eval_zero I).mp hI0
  have hAz : A₁.eval 0 = 0 := (Yau.Proofs.Y01Aux.fixesZero_iff_eval_zero A₁).mp hA₁0
  have hG0 : G 0 = 0 := by simp only [G, hIz, hF0, hAz]
  have hFI : AnalyticAt ℂ (F ∘ I.eval) 0 := by
    have hF' : AnalyticAt ℂ F (I.eval 0) := by simpa only [hIz] using hF
    exact hF'.comp (polynomial_eval_analyticAt I 0)
  have hG : AnalyticAt ℂ G 0 := by
    have H : AnalyticAt ℂ (A₁.eval ∘ (F ∘ I.eval)) 0 :=
      (polynomial_eval_analyticAt A₁ ((F ∘ I.eval) 0)).comp hFI
    exact H
  have hSG : GermJetEq S.eval G d := normalized_polynomial_germ hF hF0 hQ0 hI0 hQF
  have hCoeff (a : Fin n →₀ ℕ) (ha : a.degree ≤ d - 1) :
      S.jacDet.coeff a = (C c).coeff a := by
    have H := hOrder a (by omega)
    change S.jacDet.coeff a - (C c).coeff a = 0 at H
    exact sub_eq_zero.mp H
  have hSdet : ScalarJetEq (scalarEval S.jacDet) (fun _ => c) (d - 1) := by
    intro m hm
    have H := Yau.Proofs.Y01Aux.scalar_jetEq_iteratedFDeriv
      (p := S.jacDet) (q := C c) (d := d - 1)
      hCoeff hm
    have hpolyEq : Yau.Proofs.Y01Aux.polyEval S.jacDet = scalarEval S.jacDet := rfl
    have hconst : Yau.Proofs.Y01Aux.polyEval (C c : MvPolynomial (Fin n) ℂ) =
        (fun _ : ComplexVector n => c) := by funext z; simp [Yau.Proofs.Y01Aux.polyEval]
    simpa only [hpolyEq, hconst] using H
  have hJ := germJetEq_jacobian_det hd
    ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff S).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt hG.contDiffAt hSG
  have hSfun : (fun z => LinearMap.det (fderiv ℂ S.eval z).toLinearMap) = scalarEval S.jacDet :=
    funext (fun z => (scalarEval_jacDet S z).symm)
  have hGdet : ScalarJetEq (fun z => LinearMap.det (fderiv ℂ G z).toLinearMap)
      (fun _ => c) (d - 1) := by
    apply scalarJetEq_trans (scalarJetEq_symm hJ)
    simpa only [hSfun] using hSdet
  exact exists_constant_volume_taylor hd hG hG0 hc hGdet

end Yau.Proofs.Y05Aux
