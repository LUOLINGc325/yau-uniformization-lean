import Yau.Proofs.Y01GermSandwich

/-! Both actual finite coordinate polynomials represent the same total
coordinate transition, independently of its eventual model realization. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem coordinate_transition_germ_total
    {Anext Ainv nextCorrection inverseCorrection : PolyMap n} {T Tnext : Herm n}
    {F : ComplexVector n → ComplexVector n}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0)
    (hAinv : Ainv.FixesZero) (hqinv : inverseCorrection.FixesZero) :
    GermJetEq ((coordinateJet d Anext nextCorrection Tnext).eval ∘ F ∘
        (inverseCoordinateJet d Ainv inverseCorrection T).eval)
      (nextCorrection.eval ∘ (linearPoly Tnext).eval ∘ Anext.eval ∘ F ∘ Ainv.eval ∘
        (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) d := by
  let N := nextCorrection.comp ((linearPoly Tnext).comp Anext)
  let I := Ainv.comp ((linearPoly T⁻¹).comp inverseCorrection)
  let Hnext := coordinateJet d Anext nextCorrection Tnext
  let Hinv := inverseCoordinateJet d Ainv inverseCorrection T
  have hNfun : (nextCorrection.eval ∘ (linearPoly Tnext).eval ∘ Anext.eval) = N.eval := by
    funext z
    change _ = (nextCorrection.comp ((linearPoly Tnext).comp Anext)).eval z
    simp only [polyMap_eval_comp]
    rfl
  have hIfun : (Ainv.eval ∘ (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) = I.eval := by
    funext z
    change _ = (Ainv.comp ((linearPoly T⁻¹).comp inverseCorrection)).eval z
    simp only [polyMap_eval_comp]
    rfl
  have hNGerm : GermJetEq Hnext.eval N.eval d :=
    germJetEq_of_function_eq rfl hNfun (coordinateJet_germJetEq_total (d := d) Anext nextCorrection Tnext)
  have hIGerm : GermJetEq Hinv.eval I.eval d :=
    germJetEq_of_function_eq rfl hIfun
      (inverseCoordinateJet_germJetEq_total (d := d) (T := T) (Ainv := Ainv) hqinv)
  have hIzero : I.FixesZero := comp_fixesZero hAinv
    (comp_fixesZero (linearPoly_fixesZero _) hqinv)
  have hHizero : Hinv.FixesZero := inverseCoordinateJet_fixesZero hAinv hqinv
  have htotal := germ_coordinate_transition_congr hF hF0
    (polyMap_contDiffAt Hnext) (polyMap_contDiffAt N)
    (polyMap_contDiffAt Hinv) (polyMap_contDiffAt I)
    ((fixesZero_iff_eval_zero _).1 hHizero) ((fixesZero_iff_eval_zero _).1 hIzero) hNGerm hIGerm
  have hRight : (N.eval ∘ F ∘ I.eval) =
      (nextCorrection.eval ∘ (linearPoly Tnext).eval ∘ Anext.eval ∘ F ∘ Ainv.eval ∘
        (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) := by
    funext z
    change (nextCorrection.comp ((linearPoly Tnext).comp Anext)).eval
      (F ((Ainv.comp ((linearPoly T⁻¹).comp inverseCorrection)).eval z)) = _
    simp only [polyMap_eval_comp]
    rfl
  exact germJetEq_of_function_eq rfl hRight htotal

end Yau.Proofs.Y01Aux
