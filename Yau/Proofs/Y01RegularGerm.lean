import Yau.Proofs.Y01GermSandwich
import Yau.Proofs.Y01CorrectionData

/-! The original Y06 jet equation is cancelled using its own inverse
correction, retaining the same model and aligned jump. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem germ_postcompose_inverse
    {G q qinv : PolyMap n} {B : ComplexVector n → ComplexVector n}
    (hq : q.FixesZero) (hqi : qinv.FixesZero)
    (hinv : PolyMap.JetEq (q.comp qinv) PolyMap.id d)
    (hB : ContDiffAt ℂ d B 0) (hmodel : GermJetEq (G.eval ∘ q.eval) B d) :
    GermJetEq G.eval (B ∘ qinv.eval) d := by
  have hq0 := (fixesZero_iff_eval_zero _).1 hq
  have hqi0 := (fixesZero_iff_eval_zero _).1 hqi
  have hGq := contDiffAt_comp_zero (d := d) (polyMap_contDiffAt (d := d) q) (polyMap_contDiffAt (d := d) G) hq0
  have hpre := germJetEq_comp (polyMap_contDiffAt (d := d) qinv) (polyMap_contDiffAt (d := d) qinv)
    hGq hB hqi0 hqi0 (germJetEq_refl qinv.eval d) hmodel
  have hinner : GermJetEq (q.eval ∘ qinv.eval) id d := by
    rw [← polyMap_eval_comp_fun, ← polyMap_eval_id]
    exact jetEq_germJetEq hinv
  have hinnerSmooth := contDiffAt_comp_zero (d := d) (polyMap_contDiffAt (d := d) qinv) (polyMap_contDiffAt (d := d) q) hqi0
  have hinner0 : (q.eval ∘ qinv.eval) 0 = 0 := by simp only [Function.comp_apply, hqi0, hq0]
  have hcancel := germJetEq_comp hinnerSmooth contDiffAt_id
    (polyMap_contDiffAt (d := d) G) (polyMap_contDiffAt (d := d) G) hinner0 rfl
    hinner (germJetEq_refl G.eval d)
  have hcancel' : GermJetEq (G.eval ∘ q.eval ∘ qinv.eval) G.eval d := by
    simpa only [Function.comp_assoc, Function.comp_id] using hcancel
  exact germJetEq_trans (germJetEq_symm hcancel') (by
    simpa only [Function.comp_assoc] using hpre)

theorem regular_model_transition_germ
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {D J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar : ℕ} {s : ℕ → ℝ}
    {C : ℝ} {Q : JetData n} (hd : 1 ≤ d)
    (hQ : RegularJetSolution Fhat D J w active d Dstar s C Q)
    {k : ℕ} (hk : active k) (hJ : IsUnit (J k))
    (hF : ContDiffAt ℂ d (Fhat k) 0) (hF0 : Fhat k 0 = 0) :
    GermJetEq ((linearPoly (J k)).comp (Q.model k)).eval
      ((Q.correction (k + 1)).eval ∘ (linearPoly (J k)).eval ∘ Fhat k ∘
        (Q.inverseJet k).eval) d := by
  obtain ⟨hqlin, hqdeg, hqvol, hqideg, hqizero, hqleft, hqright,
    hforbidden, hmzero, hmlin, hallowed, hauto, hmdeg, hmideg, hjac, hconj, hnorm⟩ := hQ.2 k hk
  have hnext := (correction_data_of_regularJetSolution hd hQ (k + 1)).1.1
  have hq0 := (fixesZero_iff_eval_zero _).1 hqvol.1
  have hm0 := (fixesZero_iff_eval_zero _).1 hmzero
  have hn0 := (fixesZero_iff_eval_zero _).1 hnext
  let B := (Q.correction (k + 1)).eval ∘ (linearPoly (J k)).eval ∘ Fhat k
  have hJB := contDiffAt_comp_zero (d := d) hF (polyMap_contDiffAt (d := d) (linearPoly (J k))) hF0
  have hJF0 : ((linearPoly (J k)).eval ∘ Fhat k) 0 = 0 := by
    simp only [Function.comp_apply, hF0, linearPoly_eval_zero]
  have hB : ContDiffAt ℂ d B 0 :=
    contDiffAt_comp_zero (d := d) hJB (polyMap_contDiffAt (d := d) (Q.correction (k + 1))) hJF0
  have hB0 : B 0 = 0 := by simp only [B, Function.comp_apply, hF0, linearPoly_eval_zero, hn0]
  have hR : ContDiffAt ℂ d ((linearPoly (J k)⁻¹).eval ∘ B) 0 :=
    contDiffAt_comp_zero (d := d) hB (polyMap_contDiffAt (d := d) (linearPoly (J k)⁻¹)) hB0
  have hR0 : ((linearPoly (J k)⁻¹).eval ∘ B) 0 = 0 := by
    simp only [Function.comp_apply, hB0, linearPoly_eval_zero]
  have hMQ := contDiffAt_comp_zero (d := d) (polyMap_contDiffAt (d := d) (Q.correction k))
    (polyMap_contDiffAt (d := d) (Q.model k)) hq0
  have hMQ0 : ((Q.model k).eval ∘ (Q.correction k).eval) 0 = 0 := by
    simp only [Function.comp_apply, hq0, hm0]
  have hRfun :
      (fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((J k)⁻¹)
        ((Q.correction (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) (Fhat k z)))) =
      (linearPoly (J k)⁻¹).eval ∘ B := by
    funext z
    calc
      _ = (linearPoly (J k)⁻¹).eval ((Q.correction (k + 1)).eval
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) (Fhat k z))) :=
        (linearPoly_eval _ _).symm
      _ = (linearPoly (J k)⁻¹).eval ((Q.correction (k + 1)).eval
          ((linearPoly (J k)).eval (Fhat k z))) :=
        congrArg (fun v => (linearPoly (J k)⁻¹).eval ((Q.correction (k + 1)).eval v))
          (linearPoly_eval _ _).symm
      _ = _ := rfl
  have hconj' : GermJetEq ((Q.model k).eval ∘ (Q.correction k).eval)
      ((linearPoly (J k)⁻¹).eval ∘ B) d :=
    germJetEq_of_function_eq rfl hRfun hconj
  have hL := germJetEq_comp hMQ hR (polyMap_contDiffAt (d := d) (linearPoly (J k)))
    (polyMap_contDiffAt (d := d) (linearPoly (J k))) hMQ0 hR0 hconj'
    (germJetEq_refl (linearPoly (J k)).eval d)
  have hunit : (J k) * (J k)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJ)
  have hcancel : (linearPoly (J k)).eval ∘ (linearPoly (J k)⁻¹).eval = id := by
    funext z
    calc
      _ = ((linearPoly (J k)).comp (linearPoly (J k)⁻¹)).eval z :=
        (polyMap_eval_comp _ _ _).symm
      _ = z := by
        rw [linearPoly_comp, hunit, linearPoly_one]
        exact congrFun polyMap_eval_id z
  have hLfun : (linearPoly (J k)).eval ∘ ((Q.model k).eval ∘ (Q.correction k).eval) =
      ((linearPoly (J k)).comp (Q.model k)).eval ∘ (Q.correction k).eval := by
    funext z
    exact (polyMap_eval_comp _ _ _).symm
  have hRfun' : (linearPoly (J k)).eval ∘ ((linearPoly (J k)⁻¹).eval ∘ B) = B := by
    funext z
    exact congrFun hcancel (B z)
  have hL' : GermJetEq
      (((linearPoly (J k)).comp (Q.model k)).eval ∘ (Q.correction k).eval) B d :=
    germJetEq_of_function_eq hLfun hRfun' hL
  have h := germ_postcompose_inverse hqvol.1 hqizero hqleft hB hL'
  simpa only [B, Function.comp_assoc] using h

end Yau.Proofs.Y01Aux
