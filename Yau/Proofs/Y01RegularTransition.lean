import Yau.Proofs.Y01RegularGerm
import Yau.Proofs.Y01RegularJump
import Yau.Proofs.Y01PrimaryCoordinates
import Yau.Proofs.Y01CoordinateTransition

/-! The regular model from the original Y06 output represents the actual
transition between the same finite primary coordinate polynomials. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem regular_model_coordinate_transition
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ}
    {A Ainv : ℕ → PolyMap n} {E : Frames n} {L : Changes n} {reg active : ℕ → Prop}
    {w : ℕ → Fin n → ℝ} {macroIndex : ℕ → ℕ} {S : ℕ → ℝ} {C c Cq : ℝ}
    {Dstar : ℕ} {Q : JetData n} (hd : 1 ≤ d)
    (hE : SingularFrames F tk E)
    (hL : ∀ k, reg k → ChangeAt (diagonal F tk E) w macroIndex S C c L k)
    (hQ : RegularJetSolution (normalizedRegularTransition F tk A Ainv E L)
      (diagonal F tk E) (fun k => if reg (k + 1) then alignedJump E L k else 1)
      w active d Dstar s Cq Q)
    {k : ℕ} (hk : active k) (hreg : reg k)
    (hF : ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0)
    (hF0 : F (tk k) (tk (k + 1)) 0 = 0)
    (hAnext : (A (k + 1)).FixesZero) (hAinv : (Ainv k).FixesZero) :
    GermJetEq ((linearPoly (if reg (k + 1) then alignedJump E L k else 1)).comp (Q.model k)).eval
      ((coordinateJet d (A (k + 1)) (Q.correction (k + 1)) (primaryDerivative reg E L (k + 1))).eval ∘
        F (tk k) (tk (k + 1)) ∘
        (inverseCoordinateJet d (Ainv k) (Q.inverseJet k) (primaryDerivative reg E L k)).eval) d := by
  let T := primaryDerivative reg E L
  let J := fun k => if reg (k + 1) then alignedJump E L k else 1
  let Fhat := normalizedRegularTransition F tk A Ainv E L
  let R := E.start k * (L.minus k)⁻¹
  let B := L.plus k * (E.finish k).conjTranspose
  let I := (Ainv k).comp (linearPoly R)
  let N := (linearPoly B).comp (A (k + 1))
  have hIzero : I.FixesZero := comp_fixesZero hAinv (linearPoly_fixesZero _)
  have hNzero : N.FixesZero := comp_fixesZero (linearPoly_fixesZero _) hAnext
  have hFhatFun : Fhat k = N.eval ∘ F (tk k) (tk (k + 1)) ∘ I.eval := by
    funext z
    change _ = ((linearPoly B).comp (A (k + 1))).eval
      (F (tk k) (tk (k + 1)) (((Ainv k).comp (linearPoly R)).eval z))
    simp only [polyMap_eval_comp, linearPoly_eval]
    rfl
  have hI0 := (fixesZero_iff_eval_zero _).1 hIzero
  have hN0 := (fixesZero_iff_eval_zero _).1 hNzero
  have hFI : ContDiffAt ℂ d (F (tk k) (tk (k + 1)) ∘ I.eval) 0 :=
    contDiffAt_comp_zero (polyMap_contDiffAt I) hF hI0
  have hFI0 : (F (tk k) (tk (k + 1)) ∘ I.eval) 0 = 0 := by
    simp only [Function.comp_apply, hI0, hF0]
  have hFhat : ContDiffAt ℂ d (Fhat k) 0 := by
    rw [hFhatFun]
    exact contDiffAt_comp_zero hFI (polyMap_contDiffAt N) hFI0
  have hFhat0 : Fhat k 0 = 0 := by
    rw [hFhatFun]
    simp only [Function.comp_apply, hI0, hF0, hN0]
  have hJ : IsUnit (J k) := regular_alignedJump_isUnit hE hL hreg
  have hRegular := regular_model_transition_germ hd hQ hk hJ hFhat hFhat0
  have hqdata := correction_data_of_regularJetSolution hd hQ k
  have hqi : (Q.inverseJet k).FixesZero := hqdata.2.1.1
  have hRaw := coordinate_transition_germ_total (Anext := A (k + 1)) (T := T k) (Tnext := T (k + 1))
    (nextCorrection := Q.correction (k + 1)) (inverseCorrection := Q.inverseJet k)
    hF hF0 hAinv hqi
  have hNorm := normalized_primary_transition (F := F) (tk := tk) (A := A) (Ainv := Ainv) hreg
    (hE k).2.2.1 (hE k).2.2.2.1 (plus_change_isUnit (hL k hreg))
  have hSame :
      ((Q.correction (k + 1)).eval ∘ (linearPoly (J k)).eval ∘ Fhat k ∘ (Q.inverseJet k).eval) =
      ((Q.correction (k + 1)).eval ∘ (linearPoly (T (k + 1))).eval ∘ (A (k + 1)).eval ∘
        F (tk k) (tk (k + 1)) ∘ (Ainv k).eval ∘ (linearPoly (T k)⁻¹).eval ∘ (Q.inverseJet k).eval) := by
    have h := congrArg (fun Z : ComplexVector n → ComplexVector n =>
      (Q.correction (k + 1)).eval ∘ Z ∘ (Q.inverseJet k).eval) hNorm.symm
    exact h
  have hRegular' := germJetEq_of_function_eq rfl hSame hRegular
  exact germJetEq_trans hRegular' (germJetEq_symm hRaw)

end Yau.Proofs.Y01Aux
