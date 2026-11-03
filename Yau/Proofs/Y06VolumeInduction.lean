import Yau.Proofs.Y01VolumeComposition
import Yau.Proofs.Y06FiniteBackward

/-! Volume follows from the complete jet identity and the exact model
Jacobian. The forbidden projection is not assumed to preserve volume. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux

variable {n d : ℕ}

theorem positiveJacFlat_linearPolynomial (A : Herm n) (d : ℕ) :
    positiveJacFlat (linearPolynomial A) d := by
  intro β hβ hβd
  change (linearPoly A).jacDet.coeff β = 0
  rw [linearPoly_jacDet, coeff_C]
  have hne : β ≠ 0 := by intro hz; subst β; simp at hβ
  exact ite_eq_right (Ne.symm hne)

theorem volume_of_backward_jet_identity
    (P H Hnext g : PolyMap n) (J : Herm n) (hd : 1 ≤ d)
    (hP : IsConstantVolumeJet P d) (hNext : IsConstantVolumeJet Hnext d)
    (hH0 : H.FixesZero) (hHdegree : H.degree ≤ d) (hHlinear : H.linearPart = 1)
    (hg0 : g.FixesZero) (hgdet : g.linearPart.det ≠ 0)
    (hgjac : g.jacDet = C g.linearPart.det)
    (hidentity : PolyMap.JetEq (g.comp H)
      ((linearPolynomial J⁻¹).comp (Hnext.comp ((linearPolynomial J).comp P))) d) :
    IsConstantVolumeJet H d := by
  let R₁ := (linearPolynomial J).comp P
  let R₂ := Hnext.comp R₁
  let R := (linearPolynomial J⁻¹).comp R₂
  have hR₁zero : R₁.FixesZero := comp_fixesZero (linearPoly_fixesZero J) hP.1
  have hR₂zero : R₂.FixesZero := comp_fixesZero hNext.1 hR₁zero
  have hR₁flat : positiveJacFlat R₁ d :=
    positiveJacFlat_comp (positiveJacFlat_linearPolynomial J d) hP.2.2.2 hP.1
  have hR₂flat : positiveJacFlat R₂ d := positiveJacFlat_comp hNext.2.2.2 hR₁flat hR₁zero
  have hRflat : positiveJacFlat R d :=
    positiveJacFlat_comp (positiveJacFlat_linearPolynomial J⁻¹ d) hR₂flat hR₂zero
  have hRlinear : R.linearPart = g.linearPart := by
    have hlin := jetEq_linearPart hd hidentity
    rw [comp_linearPart hg0 hH0, hHlinear, mul_one] at hlin
    exact hlin.symm
  have hleftjac : (g.comp H).jacDet = C g.linearPart.det * H.jacDet := by
    rw [jacDet_comp, hgjac, bind₁_C_right]
  have hdiff : scalarOrderAtLeast d ((g.comp H).jacDet - R.jacDet) :=
    jacDet_order_of_jetEq hidentity
  have hconstant : scalarOrderAtLeast d (R.jacDet - C g.linearPart.det) := by
    rw [← hRlinear]
    exact jacDet_order_constant hRflat
  have hsum := scalarOrderAtLeast_add hdiff hconstant
  have heq : ((g.comp H).jacDet - R.jacDet) + (R.jacDet - C g.linearPart.det) =
      C g.linearPart.det * H.jacDet - C g.linearPart.det := by
    rw [hleftjac]
    ring
  rw [heq] at hsum
  refine ⟨hH0, hHdegree, ?_, ?_⟩
  · rw [hHlinear, Matrix.det_one]
    exact one_ne_zero
  · intro β hβ hβd
    change 1 ≤ β.degree at hβ
    change β.degree ≤ d - 1 at hβd
    have hne : β ≠ 0 := by intro hz; subst β; simp at hβ
    have hz := hsum β (by omega)
    change (C g.linearPart.det * H.jacDet).coeff β - (C g.linearPart.det).coeff β = 0 at hz
    rw [coeff_C_mul, coeff_C, ite_eq_right (Ne.symm hne), sub_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hgdet

end Yau.Proofs.Y06Aux
