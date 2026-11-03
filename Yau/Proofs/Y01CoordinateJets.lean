import Yau.Proofs.Y01InverseJets
import Yau.Proofs.Y01PrimaryAlgebra

/-! The total primary coordinate polynomial and its inverse jet are built
from the coherent-volume and homological polynomials themselves. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Proofs.Y02Aux Yau.Blueprint

variable {n : ℕ}

def coordinateJet (d : ℕ) (A correction : PolyMap n) (T : Herm n) : PolyMap n :=
  jetComp d correction (jetComp d (linearPoly T) A)

def inverseCoordinateJet (d : ℕ) (Ainv inverseCorrection : PolyMap n) (T : Herm n) : PolyMap n :=
  jetComp d (jetComp d Ainv (linearPoly T⁻¹)) inverseCorrection

theorem coordinateJet_linearPart {d : ℕ} (hd : 1 ≤ d)
    {A correction : PolyMap n} {T : Herm n}
    (hA : A.FixesZero) (hcorrection : correction.FixesZero)
    (hAlinear : A.linearPart = 1) (hCorrectionLinear : correction.linearPart = 1) :
    (coordinateJet d A correction T).linearPart = T := by
  unfold coordinateJet
  rw [jetComp_linearPart hd hcorrection (jetComp_fixesZero (linearPoly_fixesZero T) hA),
    jetComp_linearPart hd (linearPoly_fixesZero T) hA, linearPoly_linearPart, hAlinear,
    hCorrectionLinear, Matrix.mul_one, Matrix.one_mul]

theorem coordinateJet_inverses {d : ℕ}
    {A Ainv correction inverseCorrection : PolyMap n} {T : Herm n}
    (hA : A.FixesZero) (hAinv : Ainv.FixesZero)
    (hq : correction.FixesZero) (hqinv : inverseCorrection.FixesZero)
    (hAleft : PolyMap.JetEq (A.comp Ainv) PolyMap.id d)
    (hAright : PolyMap.JetEq (Ainv.comp A) PolyMap.id d)
    (hqleft : PolyMap.JetEq (correction.comp inverseCorrection) PolyMap.id d)
    (hqright : PolyMap.JetEq (inverseCorrection.comp correction) PolyMap.id d)
    (hT : T.det ≠ 0) :
    PolyMap.JetEq ((coordinateJet d A correction T).comp
      (inverseCoordinateJet d Ainv inverseCorrection T)) PolyMap.id d ∧
    PolyMap.JetEq ((inverseCoordinateJet d Ainv inverseCorrection T).comp
      (coordinateJet d A correction T)) PolyMap.id d := by
  have hauto := linearPoly_automorphism T hT
  have hlinLeft : PolyMap.JetEq ((linearPoly T).comp (linearPoly T⁻¹)) PolyMap.id d := by
    rw [hauto.1]
    exact jetEq_refl _ _
  have hlinRight : PolyMap.JetEq ((linearPoly T⁻¹).comp (linearPoly T)) PolyMap.id d := by
    rw [hauto.2]
    exact jetEq_refl _ _
  have hinnerLeft := inverse_jet_jetComp hlinLeft hAleft (linearPoly_fixesZero T⁻¹) hAinv
  have hinnerRight := inverse_jet_jetComp hAright hlinRight hA (linearPoly_fixesZero T)
  refine ⟨?_, ?_⟩
  · exact inverse_jet_jetComp hqleft hinnerLeft hqinv
      (jetComp_fixesZero hAinv (linearPoly_fixesZero T⁻¹))
  · exact inverse_jet_jetComp hinnerRight hqright
      (jetComp_fixesZero (linearPoly_fixesZero T) hA) hq

theorem coordinateJet_fixesZero {d : ℕ} {A correction : PolyMap n} {T : Herm n}
    (hA : A.FixesZero) (hq : correction.FixesZero) :
    (coordinateJet d A correction T).FixesZero :=
  jetComp_fixesZero hq (jetComp_fixesZero (linearPoly_fixesZero T) hA)

theorem inverseCoordinateJet_fixesZero {d : ℕ} {Ainv inverseCorrection : PolyMap n} {T : Herm n}
    (hAinv : Ainv.FixesZero) (hqinv : inverseCorrection.FixesZero) :
    (inverseCoordinateJet d Ainv inverseCorrection T).FixesZero :=
  jetComp_fixesZero (jetComp_fixesZero hAinv (linearPoly_fixesZero T⁻¹)) hqinv

theorem coordinateJet_degree (d : ℕ) (A correction : PolyMap n) (T : Herm n) :
    (coordinateJet d A correction T).degree ≤ d := jetComp_degree _ _ _

theorem inverseCoordinateJet_degree (d : ℕ) (Ainv inverseCorrection : PolyMap n) (T : Herm n) :
    (inverseCoordinateJet d Ainv inverseCorrection T).degree ≤ d := jetComp_degree _ _ _

theorem coordinateJet_jetEq_total {d : ℕ} {A correction : PolyMap n} {T : Herm n} :
    PolyMap.JetEq (coordinateJet d A correction T)
      (correction.comp ((linearPoly T).comp A)) d :=
  jetEq_trans (jetComp_jetEq d _ _) (jetEq_comp_left correction (jetComp_jetEq d _ _))

end Yau.Proofs.Y01Aux
