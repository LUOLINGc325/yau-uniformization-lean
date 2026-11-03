import Yau.Proofs.Y01CoordinateGerms

/-! The inverse coordinate jet has the genuine inverse primary derivative;
this follows from the original two-sided inverse jets, without an estimate. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem inverse_jet_linearPart_of_one {P Pinv : PolyMap n}
    (hd : 1 ≤ d) (hP : P.FixesZero) (hI : Pinv.FixesZero)
    (hlinear : P.linearPart = 1) (hinv : PolyMap.JetEq (P.comp Pinv) PolyMap.id d) :
    Pinv.linearPart = 1 := by
  have h := jetEq_linearPart hd hinv
  rw [comp_linearPart hP hI, hlinear, Matrix.one_mul, id_linearPart] at h
  exact h

theorem inverseCoordinateJet_linearPart
    {Ainv inverseCorrection : PolyMap n} {T : Herm n} (hd : 1 ≤ d)
    (hA : Ainv.FixesZero) (hq : inverseCorrection.FixesZero)
    (hAlinear : Ainv.linearPart = 1) (hqlinear : inverseCorrection.linearPart = 1) :
    (inverseCoordinateJet d Ainv inverseCorrection T).linearPart = T⁻¹ := by
  unfold inverseCoordinateJet
  rw [jetComp_linearPart hd (jetComp_fixesZero hA (linearPoly_fixesZero T⁻¹)) hq,
    jetComp_linearPart hd hA (linearPoly_fixesZero T⁻¹), linearPoly_linearPart,
    hAlinear, hqlinear, Matrix.one_mul, Matrix.mul_one]

end Yau.Proofs.Y01Aux
