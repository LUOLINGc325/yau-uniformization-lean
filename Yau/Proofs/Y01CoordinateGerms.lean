import Yau.Proofs.Y01CoordinateJets
import Yau.Proofs.Y01GermConjugacy
import Yau.Proofs.Y01LinearEvaluation

/-! The constructed coordinate polynomials are precisely the degree-d jets
of the total primary coordinate germ and its inverse. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Proofs.Y02Aux Yau.Blueprint
open scoped ContDiff

variable {n d : ℕ}

theorem contDiffAt_comp_zero {f g : ComplexVector n → ComplexVector n}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0) (hf0 : f 0 = 0) :
    ContDiffAt ℂ d (g ∘ f) 0 := by
  have hgF : ContDiffAt ℂ d g (f 0) := by simpa only [hf0] using hg
  exact hgF.comp 0 hf

theorem polyMap_contDiffAt (P : PolyMap n) : ContDiffAt ℂ d P.eval 0 :=
  ((polyMap_eval_contDiff P).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt

theorem coordinateJet_germJetEq_total (A correction : PolyMap n) (T : Herm n) :
    GermJetEq (coordinateJet d A correction T).eval
      (correction.eval ∘ (linearPoly T).eval ∘ A.eval) d := by
  have h := jetEq_germJetEq (coordinateJet_jetEq_total (d := d) (A := A) (correction := correction) (T := T))
  simpa only [polyMap_eval_comp_fun] using h

theorem inverseCoordinateJet_jetEq_total {Ainv inverseCorrection : PolyMap n} {T : Herm n}
    (hq : inverseCorrection.FixesZero) :
    PolyMap.JetEq (inverseCoordinateJet d Ainv inverseCorrection T)
      (Ainv.comp ((linearPoly T⁻¹).comp inverseCorrection)) d := by
  have hi := jetComp_jetEq d Ainv (linearPoly T⁻¹)
  have ho := jetComp_jetEq d (jetComp d Ainv (linearPoly T⁻¹)) inverseCorrection
  have h := jetEq_trans ho (jetEq_comp_right hi hq)
  simpa only [inverseCoordinateJet, comp_assoc] using h

theorem inverseCoordinateJet_germJetEq_total {Ainv inverseCorrection : PolyMap n} {T : Herm n}
    (hq : inverseCorrection.FixesZero) :
    GermJetEq (inverseCoordinateJet d Ainv inverseCorrection T).eval
      (Ainv.eval ∘ (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) d := by
  have h := jetEq_germJetEq (inverseCoordinateJet_jetEq_total (d := d) (Ainv := Ainv)
    (inverseCorrection := inverseCorrection) (T := T) hq)
  simpa only [polyMap_eval_comp_fun] using h

theorem linearPoly_eval_zero (T : Herm n) : (linearPoly T).eval 0 = 0 :=
  (fixesZero_iff_eval_zero _).1 (linearPoly_fixesZero T)

end Yau.Proofs.Y01Aux
