import Yau.Proofs.Y01AssembledModels
import Yau.Proofs.Y01TransitionInputs

/-! The actual assembled sequence has the original jet conjugacy on every
step, including the finite early regular prefix realized by Y02. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem assembled_models_original_conjugacy
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {reg : ℕ → Prop} {L : Changes n}
    {w : ℕ → Fin n → ℝ} {macroIndex : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ}
    (hL : ∀ k, reg k → ChangeAt (diagonal F tk E) w macroIndex S C c L k)
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk s d r last logs B ell Evol A Ainv V)
    {kLate Dstar : ℕ} {Cq : ℝ} {qsol : JetData n} (hd : 1 ≤ d)
    (hQ : RegularJetSolution (normalizedRegularTransition F tk A Ainv E L)
      (diagonal F tk E) (fun k => if reg (k + 1) then alignedJump E L k else 1)
      w (fun k => kLate ≤ k ∧ reg k) d Dstar s Cq qsol)
    (hF : ∀ k, ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0)
    (hF0 : ∀ k, F (tk k) (tk (k + 1)) 0 = 0)
    {R : ℕ → PolyMap n}
    (hR : ∀ k, PolyMap.JetEq (R k)
      (badStepJet d (qsol.correction (k + 1)) (V k) (qsol.inverseJet k)
        (primaryDerivative reg E L k) (primaryDerivative reg E L (k + 1))) d) :
    let T := primaryDerivative reg E L
    let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
    let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
    let J := fun k => if reg (k + 1) then alignedJump E L k else 1
    let G := assembledModel (fun k => kLate ≤ k ∧ reg k) J qsol R
    ∀ k, GermJetEq ((H (k + 1)).eval ∘ F (tk k) (tk (k + 1))) ((G k).eval ∘ (H k).eval) d := by
  let T := primaryDerivative reg E L
  let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
  let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
  let J := fun k => if reg (k + 1) then alignedJump E L k else 1
  let active := fun k => kLate ≤ k ∧ reg k
  have hCoord := coordinate_data_from_original_outputs (reg := reg) hE hL hVol hd hQ
  have hInputs := badStepJet_data_from_original_outputs (reg := reg) hE hL hVol hd hQ hF hF0
  dsimp only
  intro k
  obtain ⟨hH0, hI0, hHdegree, hIdegree, hHlinear, hIlinear, hTunit, hHleft, hHright⟩ := hCoord k
  have hModel : GermJetEq (assembledModel active J qsol R k).eval
      ((H (k + 1)).eval ∘ F (tk k) (tk (k + 1)) ∘ (Hinv k).eval) d := by
    by_cases hk : active k
    · obtain ⟨hellDegree, hellZero, hellSum, hellJet, hEDegree, hEJet, hAdef, hAzero, hAizero,
        hAlinear, hADegree, hAiDegree, hAleft, hAright, hVDegree, hVconst, hVjet⟩ := hVol.2.2.2.1 k
      obtain ⟨hNellDegree, hNellZero, hNellSum, hNellJet, hNEDegree, hNEJet, hNAdef, hNAzero, hNAizero,
        hNAlinear, hNADegree, hNAiDegree, hNAleft, hNAright, hNVDegree, hNVconst, hNVjet⟩ := hVol.2.2.2.1 (k + 1)
      have h := regular_model_coordinate_transition hd hE hL hQ hk hk.2 (hF k) (hF0 k) hNAzero hAizero
      simpa only [assembledModel, hk, ite_true] using h
    · have h := germJetEq_trans (jetEq_germJetEq (hR k)) (hInputs k).2
      simpa only [assembledModel, hk, ite_false] using h
  exact germ_conjugacy_of_inverse (hF k) (hF0 k) hH0 hI0 hHright hModel

end Yau.Proofs.Y01Aux
