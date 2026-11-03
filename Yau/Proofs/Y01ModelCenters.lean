import Yau.Proofs.Y01ModelConjugacy
import Yau.Proofs.Y01CenterBounds

/-! Both the explicit Y02 input jet and the actual assembled model have
the same matrix conjugacy with the original geometric center derivative. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n d : ℕ}

theorem actual_models_center_conjugacies
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
    let J := fun k => if reg (k + 1) then alignedJump E L k else 1
    let G := assembledModel (fun k => kLate ≤ k ∧ reg k) J qsol R
    let Jet := fun k => badStepJet d (qsol.correction (k + 1)) (V k) (qsol.inverseJet k) (T k) (T (k + 1))
    ∀ k, T (k + 1) * derivativeMatrix (F (tk k) (tk (k + 1))) = (Jet k).linearPart * T k ∧
      T (k + 1) * derivativeMatrix (F (tk k) (tk (k + 1))) = (G k).linearPart * T k := by
  let T := primaryDerivative reg E L
  let H := fun k => coordinateJet d (A k) (qsol.correction k) (T k)
  let Hinv := fun k => inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)
  let J := fun k => if reg (k + 1) then alignedJump E L k else 1
  let G := assembledModel (fun k => kLate ≤ k ∧ reg k) J qsol R
  let Jet := fun k => badStepJet d (qsol.correction (k + 1)) (V k) (qsol.inverseJet k) (T k) (T (k + 1))
  have hCoord := coordinate_data_from_original_outputs (reg := reg) hE hL hVol hd hQ
  have hInputs := badStepJet_data_from_original_outputs (reg := reg) hE hL hVol hd hQ hF hF0
  have hConjugacy := assembled_models_original_conjugacy (reg := reg) hE hL hVol hd hQ hF hF0 hR
  dsimp only
  intro k
  obtain ⟨hH0, hI0, hHdegree, hIdegree, hHlinear, hIlinear, hTunit, hHleft, hHright⟩ := hCoord k
  obtain ⟨hNH0, hNI0, hNHdegree, hNIdegree, hNHlinear, hNIlinear, hNTunit, hNHleft, hNHright⟩ := hCoord (k + 1)
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hd)
  have hdiff : DifferentiableAt ℂ (F (tk k) (tk (k + 1))) 0 :=
    (hF k).differentiableAt (by exact_mod_cast hd0)
  have hJetLinear := transition_jet_linearPart (J := Jet k) (Hnext := H (k + 1)) (Hinv := Hinv k)
    hd hdiff (hF0 k) hI0 (hInputs k).2
  rw [hNHlinear, hIlinear] at hJetLinear
  have hTinv : (T k)⁻¹ * T k = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hTunit)
  have hJetCenter : T (k + 1) * derivativeMatrix (F (tk k) (tk (k + 1))) = (Jet k).linearPart * T k := by
    rw [hJetLinear, Matrix.mul_assoc, hTinv, Matrix.mul_one]
  have hGCenter := center_conjugacy (H := H k) (Hnext := H (k + 1)) (G := G k)
    hd hdiff (hF0 k) hH0 (hConjugacy k)
  rw [hNHlinear, hHlinear] at hGCenter
  exact ⟨hJetCenter, hGCenter⟩

end Yau.Proofs.Y01Aux
