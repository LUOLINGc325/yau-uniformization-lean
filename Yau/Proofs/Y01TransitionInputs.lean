import Yau.Proofs.Y01CoordinateData
import Yau.Proofs.Y01BadStepGerm

/-! Construct the original Y02 input jet on every step from the actual
volume, endpoint correction and primary matrix outputs. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem badStepJet_data_from_original_outputs
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {reg : ℕ → Prop} {L : Changes n}
    {w : ℕ → Fin n → ℝ} {macroIndex : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ}
    (hL : ∀ k, reg k → ChangeAt (diagonal F tk E) w macroIndex S C c L k)
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk s d r last logs B ell Evol A Ainv V)
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {Djet Jjet : ℕ → Herm n}
    {wjet : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar : ℕ} {Cq : ℝ} {qsol : JetData n}
    (hd : 1 ≤ d) (hQ : RegularJetSolution Fhat Djet Jjet wjet active d Dstar s Cq qsol)
    (hF : ∀ k, ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0)
    (hF0 : ∀ k, F (tk k) (tk (k + 1)) 0 = 0) :
    let T := primaryDerivative reg E L
    let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
    let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
    let Jet := fun k => badStepJet d (qsol.correction (k + 1)) (V k) (qsol.inverseJet k) (T k) (T (k + 1))
    ∀ k, IsConstantVolumeJet (Jet k) d ∧
      GermJetEq (Jet k).eval ((H (k + 1)).eval ∘ F (tk k) (tk (k + 1)) ∘ (Hinv k).eval) d := by
  let T := primaryDerivative reg E L
  dsimp only
  have hCoord := coordinate_data_from_original_outputs (reg := reg) hE hL hVol hd hQ
  intro k
  obtain ⟨hellDegree, hellZero, hellSum, hellJet, hEDegree, hEJet, hAdef, hAzero, hAizero,
    hAlinear, hADegree, hAiDegree, hAleft, hAright, hVDegree, hVconst, hVjet⟩ := hVol.2.2.2.1 k
  obtain ⟨hNellDegree, hNellZero, hNellSum, hNellJet, hNEDegree, hNEJet, hNAdef, hNAzero, hNAizero,
    hNAlinear, hNADegree, hNAiDegree, hNAleft, hNAright, hNVDegree, hNVconst, hNVjet⟩ := hVol.2.2.2.1 (k + 1)
  obtain ⟨hH0, hI0, hHdegree, hIdegree, hHlinear, hIlinear, hTunit, hHleft, hHright⟩ := hCoord k
  obtain ⟨hNH0, hNI0, hNHdegree, hNIdegree, hNHlinear, hNIlinear, hNTunit, hNHleft, hNHright⟩ := hCoord (k + 1)
  have hCorr := correction_data_of_regularJetSolution hd hQ k
  have hNextCorr := correction_data_of_regularJetSolution hd hQ (k + 1)
  have hTdet : (T k).det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hTunit)
  have hNTdet : (T (k + 1)).det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hNTunit)
  refine ⟨badStepJet_constantVolume hd hNextCorr.1 hVconst hCorr.2.1 hTdet hNTdet, ?_⟩
  exact badStepJet_is_coordinate_transition (hF k) (hF0 k) hNAzero hAizero hCorr.2.1.1 hVconst.1 hVjet

end Yau.Proofs.Y01Aux
