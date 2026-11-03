import Yau.Proofs.Y01VolumeComposition

/-! Composition of the actual finite coordinate jets and their inverse jets. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Proofs.Y02Aux

variable {n : ℕ}

def jetComp (d : ℕ) (P Q : PolyMap n) : PolyMap n := truncate d (P.comp Q)

theorem jetComp_degree (d : ℕ) (P Q : PolyMap n) : (jetComp d P Q).degree ≤ d :=
  truncate_degree_le d _

theorem jetComp_jetEq (d : ℕ) (P Q : PolyMap n) :
    PolyMap.JetEq (jetComp d P Q) (P.comp Q) d := truncate_jetEq d _

theorem jetComp_fixesZero {d : ℕ} {P Q : PolyMap n} (hP : P.FixesZero) (hQ : Q.FixesZero) :
    (jetComp d P Q).FixesZero := truncate_fixesZero (comp_fixesZero hP hQ)

theorem jetComp_linearPart {d : ℕ} (hd : 1 ≤ d) {P Q : PolyMap n}
    (hP : P.FixesZero) (hQ : Q.FixesZero) :
    (jetComp d P Q).linearPart = P.linearPart * Q.linearPart := by
  rw [jetComp, truncate_linearPart hd, comp_linearPart hP hQ]

theorem inverse_jet_comp {P Pinv Q Qinv : PolyMap n} {d : ℕ}
    (hP : PolyMap.JetEq (P.comp Pinv) PolyMap.id d)
    (hQ : PolyMap.JetEq (Q.comp Qinv) PolyMap.id d) (hPinv : Pinv.FixesZero) :
    PolyMap.JetEq ((P.comp Q).comp (Qinv.comp Pinv)) PolyMap.id d := by
  have hinner : PolyMap.JetEq ((Q.comp Qinv).comp Pinv) Pinv d := by
    simpa only [id_comp] using jetEq_comp_right hQ hPinv
  have h := jetEq_trans (jetEq_comp_left P hinner) hP
  simpa only [comp_assoc] using h

theorem inverse_jet_jetComp {P Pinv Q Qinv : PolyMap n} {d : ℕ}
    (hP : PolyMap.JetEq (P.comp Pinv) PolyMap.id d)
    (hQ : PolyMap.JetEq (Q.comp Qinv) PolyMap.id d)
    (hPinv : Pinv.FixesZero) (hQinv : Qinv.FixesZero) :
    PolyMap.JetEq ((jetComp d P Q).comp (jetComp d Qinv Pinv)) PolyMap.id d := by
  apply jetEq_trans _ (inverse_jet_comp hP hQ hPinv)
  exact jetEq_comp (jetComp_jetEq d P Q) (jetComp_jetEq d Qinv Pinv)
    (jetComp_fixesZero hQinv hPinv)

theorem jetComp_constantVolume {P Q : PolyMap n} {d : ℕ}
    (hd : 1 ≤ d) (hP : IsConstantVolumeJet P d) (hQ : IsConstantVolumeJet Q d) :
    IsConstantVolumeJet (jetComp d P Q) d := isConstantVolumeJet_truncate_comp hd hP hQ

theorem jetComp_coeffNorm (d : ℕ) (P Q : PolyMap n) :
    (jetComp d P Q).coeffNorm ≤ P.coeffNorm * (1 + Q.coeffNorm) ^ P.degree :=
  (truncate_coeffNorm_le d _).trans (comp_coeffNorm_le P Q)

end Yau.Proofs.Y01Aux
