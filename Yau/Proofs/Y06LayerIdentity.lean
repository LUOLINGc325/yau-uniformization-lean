import Yau.Proofs.Y06LayerPerturbation

/-! Restore the allowed layer and advance the complete jet identity.
The forcing is the actual homogeneous discrepancy of the two sides. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

theorem right_composition_layer_update (P Hnext uNext : PolyMap n) (D J : Herm n)
    (hP : P.FixesZero) (hD : P.linearPart = D) (huNext : Homogeneous uNext m) :
    PolyMap.JetEq
      ((linearPolynomial J⁻¹).comp ((Hnext + uNext).comp ((linearPolynomial J).comp P)))
      ((linearPolynomial J⁻¹).comp (Hnext.comp ((linearPolynomial J).comp P)) +
        (linearPolynomial J⁻¹).comp (uNext.comp (linearPolynomial (J * D)))) m := by
  let U := (linearPolynomial J).comp P
  let V := linearPolynomial (J * D)
  have hU : U.FixesZero := Yau.Proofs.Y01Aux.comp_fixesZero (linearPoly_fixesZero J) hP
  have hV : V.FixesZero := linearPoly_fixesZero (J * D)
  have hUlinear : U.linearPart = J * D := by
    change ((linearPoly J).comp P).linearPart = _
    rw [Yau.Proofs.Y01Aux.comp_linearPart (linearPoly_fixesZero J) hP, linearPoly_linearPart, hD]
  have hUV : mapOrderAtLeast 2 (U - V) := by
    apply (jetEq_iff_order U V 1).mp
    have h := Yau.Proofs.Y01Aux.jetEq_linear_of_fixesZero hU
    rw [hUlinear] at h
    exact h
  have hreplace := homogeneous_comp_same_linear huNext U V hU hV hUV
  have hlinear := Yau.Proofs.Y01Aux.jetEq_comp_left (linearPolynomial J⁻¹) hreplace
  have heq : (linearPolynomial J⁻¹).comp ((Hnext + uNext).comp U) =
      (linearPolynomial J⁻¹).comp (Hnext.comp U) + (linearPolynomial J⁻¹).comp (uNext.comp U) := by
    rw [Yau.Proofs.Y02Aux.comp_add_left, linearPolynomial_comp_add]
  change PolyMap.JetEq ((linearPolynomial J⁻¹).comp ((Hnext + uNext).comp U))
    ((linearPolynomial J⁻¹).comp (Hnext.comp U) + (linearPolynomial J⁻¹).comp (uNext.comp V)) m
  rw [heq]
  exact jetEq_add (jetEq_refl _ _) hlinear

theorem complete_layer_identity (P H Hnext G u uNext v : PolyMap n) (D J : Herm n)
    (hm : 2 ≤ m) (hP : P.FixesZero) (hD : P.linearPart = D)
    (hG : G.FixesZero) (hGlinear : G.linearPart = D) (hH : tangentId H)
    (hu : Homogeneous u m) (huNext : Homogeneous uNext m) (hv : Homogeneous v m)
    (hold : PolyMap.JetEq (G.comp H)
      ((linearPolynomial J⁻¹).comp (Hnext.comp ((linearPolynomial J).comp P))) (m - 1))
    (hlayer : (linearPolynomial D).comp u + v =
      (linearPolynomial J⁻¹).comp (uNext.comp (linearPolynomial (J * D))) +
        homogeneousPart m (((linearPolynomial J⁻¹).comp (Hnext.comp ((linearPolynomial J).comp P))) - G.comp H)) :
    PolyMap.JetEq ((G + v).comp (H + u))
      ((linearPolynomial J⁻¹).comp ((Hnext + uNext).comp ((linearPolynomial J).comp P))) m := by
  let R := (linearPolynomial J⁻¹).comp (Hnext.comp ((linearPolynomial J).comp P))
  let Z := (linearPolynomial J⁻¹).comp (uNext.comp (linearPolynomial (J * D)))
  let B := homogeneousPart m (R - G.comp H)
  have hleft := complete_composition_layer_update D hm hG hGlinear hH hu hv
  have hmid : G.comp H + (linearPolynomial D).comp u + v = G.comp H + B + Z := by
    rw [add_assoc, hlayer]
    change G.comp H + (Z + B) = G.comp H + B + Z
    abel
  rw [hmid] at hleft
  have hcorrect : PolyMap.JetEq (G.comp H + B) R m :=
    firstDiscrepancy_corrects (by omega) (jetEq_symm hold)
  have hmiddle : PolyMap.JetEq (G.comp H + B + Z) (R + Z) m :=
    jetEq_add hcorrect (jetEq_refl Z m)
  have hright := right_composition_layer_update P Hnext uNext D J hP hD huNext
  exact jetEq_trans hleft (jetEq_trans hmiddle (jetEq_symm hright))

end Yau.Proofs.Y06Aux
