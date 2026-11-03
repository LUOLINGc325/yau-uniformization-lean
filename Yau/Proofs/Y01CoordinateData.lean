import Yau.Proofs.Y01CoordinateBounds
import Yau.Proofs.Y01InverseLinear

/-! Structural data of the actual primary coordinate polynomials are
constructed from the original volume and correction jets themselves. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem coordinate_data_from_original_outputs
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
    (hd : 1 ≤ d) (hQ : RegularJetSolution Fhat Djet Jjet wjet active d Dstar s Cq qsol) :
    let T := primaryDerivative reg E L
    let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
    let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
    ∀ k, (H k).FixesZero ∧ (Hinv k).FixesZero ∧ (H k).degree ≤ d ∧ (Hinv k).degree ≤ d ∧
      (H k).linearPart = T k ∧ (Hinv k).linearPart = (T k)⁻¹ ∧ IsUnit (T k) ∧
      PolyMap.JetEq ((H k).comp (Hinv k)) PolyMap.id d ∧
      PolyMap.JetEq ((Hinv k).comp (H k)) PolyMap.id d := by
  let T := primaryDerivative reg E L
  dsimp only
  intro k
  obtain ⟨hellDegree, hellZero, hellSum, hellJet, hEDegree, hEJet, hAdef, hAzero, hAizero,
    hAlinear, hADegree, hAiDegree, hAleft, hAright, hVDegree, hVconst, hVjet⟩ := hVol.2.2.2.1 k
  have hCorr := correction_data_of_regularJetSolution hd hQ k
  have hqzero := hCorr.1.1
  have hqizero := hCorr.2.1.1
  have hAiLinear := inverse_jet_linearPart_of_one hd hAzero hAizero hAlinear hAleft
  have hQiLinear := inverse_jet_linearPart_of_one hd hqzero hqizero hCorr.2.2.1 hCorr.2.2.2.1
  have hTunit : IsUnit (T k) := primaryDerivative_isUnit hE hL k
  have hTdet : (T k).det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hTunit)
  have hInverse := coordinateJet_inverses hAzero hAizero hqzero hqizero
    hAleft hAright hCorr.2.2.2.1 hCorr.2.2.2.2 hTdet
  refine ⟨coordinateJet_fixesZero hAzero hqzero, inverseCoordinateJet_fixesZero hAizero hqizero,
    coordinateJet_degree d (A k) (qsol.correction k) (T k),
    inverseCoordinateJet_degree d (Ainv k) (qsol.inverseJet k) (T k),
    coordinateJet_linearPart hd hAzero hqzero hAlinear hCorr.2.2.1,
    inverseCoordinateJet_linearPart hd hAizero hqizero hAiLinear hQiLinear,
    hTunit, hInverse.1, hInverse.2⟩

end Yau.Proofs.Y01Aux
