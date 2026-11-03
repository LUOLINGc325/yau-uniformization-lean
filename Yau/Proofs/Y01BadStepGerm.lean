import Yau.Proofs.Y01BadStepJet
import Yau.Proofs.Y01GermSandwich

/-! The bad-step input is the jet of the transition between the same total
primary coordinates; its volume polynomial is the actual Y05 output. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem badStepJet_is_coordinate_transition
    {Anext Ainv nextCorrection inverseCorrection V : PolyMap n} {T Tnext : Herm n}
    {F : ComplexVector n → ComplexVector n}
    (hF : ContDiffAt ℂ d F 0) (hF0 : F 0 = 0)
    (hAnext : Anext.FixesZero) (hAinv : Ainv.FixesZero) (hqinv : inverseCorrection.FixesZero)
    (hVzero : V.FixesZero)
    (hV : GermJetEq (Anext.eval ∘ F ∘ Ainv.eval) V.eval d) :
    GermJetEq (badStepJet d nextCorrection V inverseCorrection T Tnext).eval
      ((coordinateJet d Anext nextCorrection Tnext).eval ∘ F ∘
        (inverseCoordinateJet d Ainv inverseCorrection T).eval) d := by
  let left := nextCorrection.comp (linearPoly Tnext)
  let right := (linearPoly T⁻¹).comp inverseCorrection
  let Hnext := coordinateJet d Anext nextCorrection Tnext
  let Hinv := inverseCoordinateJet d Ainv inverseCorrection T
  let N := left.comp Anext
  let I := Ainv.comp right
  let Fvol := Anext.eval ∘ F ∘ Ainv.eval
  have hA0 := (fixesZero_iff_eval_zero _).1 hAinv
  have hAn0 := (fixesZero_iff_eval_zero _).1 hAnext
  have hV0 := (fixesZero_iff_eval_zero _).1 hVzero
  have hrightZero : right.FixesZero := comp_fixesZero (linearPoly_fixesZero _) hqinv
  have hIzero : I.FixesZero := comp_fixesZero hAinv hrightZero
  have hIz : Hinv.FixesZero := inverseCoordinateJet_fixesZero hAinv hqinv
  have hFvol : ContDiffAt ℂ d Fvol 0 := by
    have hFA := contDiffAt_comp_zero (polyMap_contDiffAt Ainv) hF hA0
    have hFA0 : (F ∘ Ainv.eval) 0 = 0 := by simp only [Function.comp_apply, hA0, hF0]
    exact contDiffAt_comp_zero hFA (polyMap_contDiffAt Anext) hFA0
  have hFvol0 : Fvol 0 = 0 := by simp only [Fvol, Function.comp_apply, hA0, hF0, hAn0]
  have hNfun : (nextCorrection.eval ∘ (linearPoly Tnext).eval ∘ Anext.eval) = N.eval := by
    funext z
    change _ = (left.comp Anext).eval z
    rw [polyMap_eval_comp]
    change _ = (nextCorrection.comp (linearPoly Tnext)).eval (Anext.eval z)
    rw [polyMap_eval_comp]
    rfl
  have hIfun : (Ainv.eval ∘ (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) = I.eval := by
    funext z
    change _ = (Ainv.comp right).eval z
    rw [polyMap_eval_comp]
    change _ = Ainv.eval (((linearPoly T⁻¹).comp inverseCorrection).eval z)
    rw [polyMap_eval_comp]
    rfl
  have hNGerm : GermJetEq Hnext.eval N.eval d :=
    germJetEq_of_function_eq rfl hNfun (coordinateJet_germJetEq_total (d := d) Anext nextCorrection Tnext)
  have hIGerm : GermJetEq Hinv.eval I.eval d :=
    germJetEq_of_function_eq rfl hIfun
      (inverseCoordinateJet_germJetEq_total (d := d) (T := T) (Ainv := Ainv) hqinv)
  have htotal := germ_coordinate_transition_congr hF hF0
    (polyMap_contDiffAt Hnext) (polyMap_contDiffAt N)
    (polyMap_contDiffAt Hinv) (polyMap_contDiffAt I)
    ((fixesZero_iff_eval_zero _).1 hIz) ((fixesZero_iff_eval_zero _).1 hIzero) hNGerm hIGerm
  have hvol := germJetEq_sandwich hFvol (polyMap_contDiffAt V)
    (polyMap_contDiffAt left) (polyMap_contDiffAt right)
    hFvol0 hV0 ((fixesZero_iff_eval_zero _).1 hrightZero) hV
  have htargetLeft : (left.eval ∘ Fvol ∘ right.eval) = (N.eval ∘ F ∘ I.eval) := by
    funext z
    simp only [Function.comp_apply, Fvol]
    change _ = (left.comp Anext).eval (F ((Ainv.comp right).eval z))
    simp only [polyMap_eval_comp]
  have hvol' : GermJetEq (N.eval ∘ F ∘ I.eval) (left.eval ∘ V.eval ∘ right.eval) d :=
    germJetEq_of_function_eq htargetLeft rfl hvol
  have htarget := germJetEq_trans htotal hvol'
  have hbadRight :
      (nextCorrection.eval ∘ (linearPoly Tnext).eval ∘ V.eval ∘
        (linearPoly T⁻¹).eval ∘ inverseCorrection.eval) = (left.eval ∘ V.eval ∘ right.eval) := by
    funext z
    change _ = (nextCorrection.comp (linearPoly Tnext)).eval
      (V.eval (((linearPoly T⁻¹).comp inverseCorrection).eval z))
    rw [polyMap_eval_comp, polyMap_eval_comp]
    rfl
  have hbad : GermJetEq (badStepJet d nextCorrection V inverseCorrection T Tnext).eval
      (left.eval ∘ V.eval ∘ right.eval) d :=
    germJetEq_of_function_eq rfl hbadRight (badStepJet_germJetEq (d := d)
      (nextCorrection := nextCorrection) (V := V) (inverseCorrection := inverseCorrection) (T := T) (Tnext := Tnext))
  exact germJetEq_trans hbad (germJetEq_symm htarget)

end Yau.Proofs.Y01Aux
