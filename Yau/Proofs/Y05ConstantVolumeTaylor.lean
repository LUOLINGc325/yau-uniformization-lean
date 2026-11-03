import Yau.Proofs.Y05VectorTaylor
import Yau.Proofs.Y05DeterminantJets
import Yau.Proofs.Y05PolynomialJacobian
import Yau.Proofs.Y01JetVolume

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment MvPolynomial
open scoped ContDiff

variable {n d : ℕ}

/-- A holomorphic germ whose genuine Jacobian jet is constant has the
constant-volume polynomial jet required by the frozen contract. -/
theorem exists_constant_volume_taylor {f : ComplexVector n → ComplexVector n}
    (hd : 1 ≤ d) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) {c : ℂ} (hc : c ≠ 0)
    (hdet : ScalarJetEq (fun z => LinearMap.det (fderiv ℂ f z).toLinearMap)
      (fun _ => c) (d - 1)) :
    ∃ V : PolyMap n, V.degree ≤ d ∧ IsConstantVolumeJet V d ∧ GermJetEq f V.eval d := by
  obtain ⟨V, hVdeg, hVjet, hV0⟩ := exists_vector_taylor hf d
  have hJ := germJetEq_jacobian_det hd
    ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff V).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt hf.contDiffAt hVjet
  have hFunV : (fun z => LinearMap.det (fderiv ℂ V.eval z).toLinearMap) =
      scalarEval V.jacDet := funext (fun z => (scalarEval_jacDet V z).symm)
  have hFunC : (fun _ : ComplexVector n => c) = scalarEval (C c) := by
    funext z; simp [scalarEval]
  have hVconst : ScalarJetEq (scalarEval V.jacDet) (scalarEval (C c)) (d - 1) := by
    simpa only [hFunV, hFunC] using scalarJetEq_trans hJ hdet
  have hCoeff0 := scalarJetEq_coefficients hVconst 0 (by simp)
  simp only [coeff_C, ite_true] at hCoeff0
  have hLin : V.linearPart.det = c :=
    (Yau.Proofs.Y01Aux.jacDet_constantCoeff V).symm.trans hCoeff0
  refine ⟨V, hVdeg, ⟨hV0 hf0, hVdeg, ?_, ?_⟩, fun m hm => (hVjet m hm).symm⟩
  · rw [hLin]
    exact hc
  · intro a ha had
    change 1 ≤ a.degree at ha
    change a.degree ≤ d - 1 at had
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    have H := scalarJetEq_coefficients hVconst a had
    simpa [coeff_C, ha0, Ne.symm ha0] using H

end Yau.Proofs.Y05Aux
