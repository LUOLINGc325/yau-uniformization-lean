import Yau.Proofs.Y01AlignmentTail
import Yau.Proofs.Y01AssembledModels
import Yau.Proofs.Y01CoordinateData

/-! After one late base construction, the SAME jets and assembled models
satisfy original RegularModelCompatibility at every later regular start. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.NodeProofs.Y07Aux Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem regularModelCompatibility_from_original_tail
    {Qclock : ℕ → ℝ} {N jBase j₀ kLate Dd Dsix Dtotal : ℕ} {M hm scale K eps : ℝ}
    (hb : jBase ≤ j₀) (hgrid : GridLayout Qclock N M hm j₀)
    (hstart : Regular Qclock N M j₀) (hOff : kLate ≤ offset Qclock N M hm jBase j₀)
    (hDmax : max Dd Dsix ≤ Dtotal)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (hOrder : RateOrder F tk E) {L : Changes n} {C c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hL : ∀ k, Regular Qclock N M (macroAt Qclock N M hm jBase k) →
      ChangeAt (diagonal F tk E) (weight Qclock N M hm scale K eps jBase (rate F tk E))
        (macroAt Qclock N M hm jBase) (macroClock hm) C c L k ∧
      (Regular Qclock N M (macroAt Qclock N M hm jBase (k + 1)) →
        JumpAt E (weight Qclock N M hm scale K eps jBase (rate F tk E)) L k))
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk (gridClock Qclock N M hm jBase) d r last logs B ell Evol A Ainv V)
    {Cq : ℝ} {qsol : JetData n} (hd : 1 ≤ d)
    (hQ : RegularJetSolution (normalizedRegularTransition F tk A Ainv E L) (diagonal F tk E)
      (fun k => if Regular Qclock N M (macroAt Qclock N M hm jBase (k + 1)) then alignedJump E L k else 1)
      (weight Qclock N M hm scale K eps jBase (rate F tk E))
      (fun k => kLate ≤ k ∧ Regular Qclock N M (macroAt Qclock N M hm jBase k))
      d Dsix (gridClock Qclock N M hm jBase) Cq qsol)
    {R Rinv : ℕ → PolyMap n} (hRdegree : ∀ k, (R k).degree ≤ Dd ∧ (Rinv k).degree ≤ Dd) :
    let off := offset Qclock N M hm jBase j₀
    let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm jBase k)
    let T := primaryDerivative reg E L
    let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
    let J := fun k => if reg (k + 1) then alignedJump E L k else 1
    let G := assembledModel (fun k => kLate ≤ k ∧ reg k) J qsol R
    let Ginv := assembledInverseModel (fun k => kLate ≤ k ∧ reg k) J qsol Rinv
    RegularModelCompatibility F (fun k => tk (off + k)) Qclock N M hm scale K eps j₀ Dtotal
      (shiftFrames off E) (shiftChanges off L) (fun k => H (off + k))
      (fun k => G (off + k)) (fun k => Ginv (off + k)) (fun k => qsol.model (off + k)) := by
  let off := offset Qclock N M hm jBase j₀
  let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm jBase k)
  let regNew := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
  let T := primaryDerivative reg E L
  let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
  let J := fun k => if reg (k + 1) then alignedJump E L k else 1
  let active := fun k => kLate ≤ k ∧ reg k
  let G := assembledModel active J qsol R
  let Ginv := assembledInverseModel active J qsol Rinv
  have hmacro k : macroAt Qclock N M hm j₀ k = macroAt Qclock N M hm jBase (off + k) :=
    (macroAt_tail Qclock N M hm hb hgrid k).symm
  have hRegEq : regNew = (fun k => reg (off + k)) := by
    funext k
    exact congrArg (Regular Qclock N M) (hmacro k)
  have hRegStart : reg off := regular_start_at_offset hb hgrid hstart
  have hmu : rate F (fun k => tk (off + k)) (shiftFrames off E) =
      (fun k => rate F tk E (off + k)) := by
    funext k i
    exact rate_shift F tk E off k i
  have hw k : weight Qclock N M hm scale K eps j₀
      (rate F (fun k => tk (off + k)) (shiftFrames off E)) k =
      weight Qclock N M hm scale K eps jBase (rate F tk E) (off + k) := by
    funext i
    rw [hmu]
    exact weight_tail Qclock N M hm scale K eps hb hgrid (rate F tk E) k i
  have hCoord := coordinate_data_from_original_outputs (reg := reg) hE (fun k hk => (hL k hk).1) hVol hd hQ
  have hDegrees := assembled_models_degree (J := J) hQ hRdegree
  change RegularModelCompatibility F (fun k => tk (off + k)) Qclock N M hm scale K eps j₀ Dtotal
    (shiftFrames off E) (shiftChanges off L) (fun k => H (off + k))
    (fun k => G (off + k)) (fun k => Ginv (off + k)) (fun k => qsol.model (off + k))
  refine ⟨singularFrames_shift hE off, rateOrder_shift hOrder off, ?_, ?_, ?_, ?_⟩
  · refine ⟨C, c, hC, hc, ?_⟩
    intro k hk
    have hkBase : reg (off + k) := Eq.mp (congrFun hRegEq k) hk
    have hBase := hL (off + k) hkBase
    refine ⟨changeAt_canonical_tail hb hgrid hBase.1, ?_⟩
    intro hkNext
    have hkNextBase : reg (off + k + 1) := by
      simpa only [Nat.add_assoc] using Eq.mp (congrFun hRegEq (k + 1)) hkNext
    exact jumpAt_canonical_tail hb hgrid (hBase.2 hkNextBase)
  · intro k
    have hHlinear := (hCoord (off + k)).2.2.2.2.1
    have hPredicate := congrArg (fun p : ℕ → Prop =>
      primaryDerivative p (shiftFrames off E) (shiftChanges off L) k) hRegEq
    have hPrimary := hPredicate.trans (primaryDerivative_shift reg E L off hRegStart k)
    exact hHlinear.trans hPrimary.symm
  · intro k
    exact ⟨(hDegrees (off + k)).1.trans hDmax, (hDegrees (off + k)).2.trans hDmax⟩
  · intro k hk
    have hkBase : reg (off + k) := Eq.mp (congrFun hRegEq k) hk
    have hkActive : active (off + k) := ⟨by omega, hkBase⟩
    obtain ⟨hqlin, hqdegree, hqvolume, hqidegree, hqizero, hqleft, hqright, hforbidden,
      hmzero, hmlinear, hallowed, hauto, hmdegree, hmidegree, hjac, hconj, hnorm⟩ := hQ.2 (off + k) hkActive
    have hCond : regNew (k + 1) = reg (off + k + 1) := by
      simpa only [Nat.add_assoc] using congrFun hRegEq (k + 1)
    have hJshift : (if regNew (k + 1) then alignedJump (shiftFrames off E) (shiftChanges off L) k else 1) =
        J (off + k) := by
      simp only [J, hCond, alignedJump_shift, Nat.add_assoc]
    have hFormula : G (off + k) =
        (linearPolynomial (if regNew (k + 1) then alignedJump (shiftFrames off E) (shiftChanges off L) k else 1)).comp
          (qsol.model (off + k)) := by
      change assembledModel active J qsol R (off + k) = _
      rw [assembledModel, if_pos hkActive, linearPolynomial_eq_linearPoly]
      exact congrArg (fun A : Herm n => (linearPoly A).comp (qsol.model (off + k))) hJshift.symm
    have hDshift := diagonal_shift F tk E off k
    have hAllowed : Allowed (qsol.model (off + k))
        (weight Qclock N M hm scale K eps j₀ (rate F (fun k => tk (off + k)) (shiftFrames off E)) k) :=
      Eq.mpr (congrArg (Allowed (qsol.model (off + k))) (hw k)) hallowed
    exact ⟨hFormula, hmzero, hmlinear.trans hDshift.symm, hAllowed,
      hjac.trans (congrArg (fun A : Herm n => (MvPolynomial.C A.det : MvPolynomial (Fin n) ℂ)) hDshift.symm)⟩

end Yau.Proofs.Y01Aux
