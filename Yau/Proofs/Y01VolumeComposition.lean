import Yau.Proofs.Y01JetVolume
import Yau.Proofs.Y01PolynomialComposition

/-! Formal composition and inverse jets preserve the required Jacobian order. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open MvPolynomial Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem positiveJacFlat_comp {P Q : PolyMap n} {d : ℕ}
    (hP : positiveJacFlat P d) (hQ : positiveJacFlat Q d) (hQzero : Q.FixesZero) :
    positiveJacFlat (P.comp Q) d := by
  have hPord := jacDet_order_constant hP
  have hQord := jacDet_order_constant hQ
  have hbind : scalarOrderAtLeast d
      (bind₁ Q P.jacDet - C P.linearPart.det) := by
    simpa only [map_sub, bind₁_C_right] using scalarOrderAtLeast_bind hPord hQzero
  have hord : scalarOrderAtLeast d
      ((P.comp Q).jacDet - C (P.linearPart.det * Q.linearPart.det)) := by
    rw [jacDet_comp, map_mul]
    have heq : bind₁ Q P.jacDet * Q.jacDet - C P.linearPart.det * C Q.linearPart.det =
        (bind₁ Q P.jacDet - C P.linearPart.det) * Q.jacDet +
          C P.linearPart.det * (Q.jacDet - C Q.linearPart.det) := by ring
    rw [heq]
    exact scalarOrderAtLeast_add (scalarOrderAtLeast_mul_right hbind _)
      (scalarOrderAtLeast_mul_left _ hQord)
  intro a ha had
  have hz := hord a (by omega)
  have ha0 : a ≠ 0 := by
    intro heq
    subst a
    simp at ha
  change (P.comp Q).jacDet.coeff a - (C (P.linearPart.det * Q.linearPart.det)).coeff a = 0 at hz
  simpa only [coeff_C, ite_eq_right (Ne.symm ha0), sub_zero] using hz

theorem isConstantVolumeJet_truncate_comp {P Q : PolyMap n} {d : ℕ}
    (hd : 1 ≤ d) (hP : IsConstantVolumeJet P d) (hQ : IsConstantVolumeJet Q d) :
    IsConstantVolumeJet (truncate d (P.comp Q)) d := by
  apply isConstantVolumeJet_truncate hd (comp_fixesZero hP.1 hQ.1)
  · rw [comp_linearPart hP.1 hQ.1, Matrix.det_mul]
    exact mul_ne_zero hP.2.2.1 hQ.2.2.1
  · exact positiveJacFlat_comp hP.2.2.2 hQ.2.2.2 hQ.1

theorem positiveJacFlat_inverseJet {P Pinv : PolyMap n} {d : ℕ}
    (hP : IsConstantVolumeJet P d) (hPinv : Pinv.FixesZero)
    (hjet : PolyMap.JetEq (P.comp Pinv) PolyMap.id d) : positiveJacFlat Pinv d := by
  have hbind : scalarOrderAtLeast d
      (bind₁ Pinv P.jacDet - C P.linearPart.det) := by
    simpa only [map_sub, bind₁_C_right] using
      scalarOrderAtLeast_bind (jacDet_order_constant hP.2.2.2) hPinv
  have hcomp : scalarOrderAtLeast d ((P.comp Pinv).jacDet - 1) := by
    simpa only [jacDet_id] using jacDet_order_of_jetEq hjet
  have hord : scalarOrderAtLeast d (C P.linearPart.det * Pinv.jacDet - 1) := by
    have heq : C P.linearPart.det * Pinv.jacDet - 1 =
        ((P.comp Pinv).jacDet - 1) -
          (bind₁ Pinv P.jacDet - C P.linearPart.det) * Pinv.jacDet := by
      rw [jacDet_comp]
      ring
    rw [heq]
    exact scalarOrderAtLeast_sub hcomp (scalarOrderAtLeast_mul_right hbind _)
  intro a ha had
  have ha0 : a ≠ 0 := by
    intro heq
    subst a
    simp at ha
  have hz := hord a (by omega)
  change (C P.linearPart.det * Pinv.jacDet).coeff a - (1 : MvPolynomial (Fin n) ℂ).coeff a = 0 at hz
  have hone : (1 : MvPolynomial (Fin n) ℂ).coeff a = 0 := by
    rw [← C_1, coeff_C, ite_eq_right (Ne.symm ha0)]
  have hmul : P.linearPart.det * Pinv.jacDet.coeff a = 0 := by
    rwa [coeff_C_mul, hone, sub_zero] at hz
  exact (mul_eq_zero.mp hmul).resolve_left hP.2.2.1

theorem id_linearPart : (PolyMap.id : PolyMap n).linearPart = 1 := by
  rw [← linearPoly_one, linearPoly_linearPart]

theorem isConstantVolumeJet_inverseJet {P Pinv : PolyMap n} {d : ℕ}
    (hd : 1 ≤ d) (hP : IsConstantVolumeJet P d) (hPinv : Pinv.FixesZero)
    (hdeg : Pinv.degree ≤ d) (hjet : PolyMap.JetEq (P.comp Pinv) PolyMap.id d) :
    IsConstantVolumeJet Pinv d := by
  refine ⟨hPinv, hdeg, ?_, positiveJacFlat_inverseJet hP hPinv hjet⟩
  have hlinear := jetEq_linearPart hd hjet
  have hdet := congrArg Matrix.det hlinear
  rw [comp_linearPart hP.1 hPinv, Matrix.det_mul, id_linearPart, Matrix.det_one] at hdet
  intro hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

end Yau.Proofs.Y01Aux
