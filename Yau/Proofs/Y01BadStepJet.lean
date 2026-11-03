import Yau.Proofs.Y01PrimaryAlgebra
import Yau.Proofs.Y01GermConjugacy

/-! The bad-step input for the original Y02 realization is explicitly
composed from the volume and endpoint correction polynomials. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Proofs.Y02Aux

variable {n : ℕ}

def badStepJet (d : ℕ) (nextCorrection V inverseCorrection : PolyMap n) (T Tnext : Herm n) : PolyMap n :=
  jetComp d nextCorrection (jetComp d (linearPoly Tnext)
    (jetComp d V (jetComp d (linearPoly T⁻¹) inverseCorrection)))

theorem badStepJet_constantVolume {d : ℕ} (hd : 1 ≤ d)
    {nextCorrection V inverseCorrection : PolyMap n} {T Tnext : Herm n}
    (hnext : IsConstantVolumeJet nextCorrection d) (hV : IsConstantVolumeJet V d)
    (hinverse : IsConstantVolumeJet inverseCorrection d)
    (hT : T.det ≠ 0) (hTnext : Tnext.det ≠ 0) :
    IsConstantVolumeJet (badStepJet d nextCorrection V inverseCorrection T Tnext) d := by
  have hTinv : T⁻¹.det ≠ 0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hT
  have hlinTinv : IsConstantVolumeJet (linearPoly T⁻¹) d := by
    simpa only [linearPolynomial_eq_linearPoly] using isConstantVolumeJet_linearPolynomial T⁻¹ hd hTinv
  have hlinNext : IsConstantVolumeJet (linearPoly Tnext) d := by
    simpa only [linearPolynomial_eq_linearPoly] using isConstantVolumeJet_linearPolynomial Tnext hd hTnext
  exact jetComp_constantVolume hd hnext (jetComp_constantVolume hd hlinNext
    (jetComp_constantVolume hd hV (jetComp_constantVolume hd hlinTinv hinverse)))

theorem badStepJet_jetEq {d : ℕ}
    {nextCorrection V inverseCorrection : PolyMap n} {T Tnext : Herm n} :
    PolyMap.JetEq (badStepJet d nextCorrection V inverseCorrection T Tnext)
      (nextCorrection.comp ((linearPoly Tnext).comp
        (V.comp ((linearPoly T⁻¹).comp inverseCorrection)))) d := by
  have h0 := jetComp_jetEq d (linearPoly T⁻¹) inverseCorrection
  have h1 := jetEq_trans (jetComp_jetEq d V _) (jetEq_comp_left V h0)
  have h2 := jetEq_trans (jetComp_jetEq d (linearPoly Tnext) _) (jetEq_comp_left (linearPoly Tnext) h1)
  exact jetEq_trans (jetComp_jetEq d nextCorrection _) (jetEq_comp_left nextCorrection h2)

theorem badStepJet_germJetEq {d : ℕ}
    {nextCorrection V inverseCorrection : PolyMap n} {T Tnext : Herm n} :
    GermJetEq (badStepJet d nextCorrection V inverseCorrection T Tnext).eval
      (nextCorrection.eval ∘ (linearPoly Tnext).eval ∘ V.eval ∘
        (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) d := by
  have h := jetEq_germJetEq (badStepJet_jetEq (d := d) (nextCorrection := nextCorrection)
    (V := V) (inverseCorrection := inverseCorrection) (T := T) (Tnext := Tnext))
  simpa only [polyMap_eval_comp_fun] using h

end Yau.Proofs.Y01Aux
