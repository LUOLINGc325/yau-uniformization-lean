import Yau.Proofs.Y01PrimaryAlgebra
import Yau.Proofs.Y01VolumeComposition

/-! The correction and inverse correction are the original Y06 polynomials,
including the identity values outside the regular set. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem correction_data_of_regularJetSolution
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {D J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {reg : ℕ → Prop} {d Dstar : ℕ} {s : ℕ → ℝ}
    {C : ℝ} {Q : JetData n} (hd : 1 ≤ d)
    (hQ : RegularJetSolution Fhat D J w reg d Dstar s C Q) :
    ∀ k, IsConstantVolumeJet (Q.correction k) d ∧
      IsConstantVolumeJet (Q.inverseJet k) d ∧ (Q.correction k).linearPart = 1 ∧
      PolyMap.JetEq ((Q.correction k).comp (Q.inverseJet k)) PolyMap.id d ∧
      PolyMap.JetEq ((Q.inverseJet k).comp (Q.correction k)) PolyMap.id d := by
  have hid : IsConstantVolumeJet (PolyMap.id : PolyMap n) d := by
    have h := isConstantVolumeJet_linearPolynomial (1 : Herm n) hd (by simp)
    simpa only [linearPolynomial_eq_linearPoly, linearPoly_one] using h
  intro k
  by_cases hk : reg k
  · obtain ⟨hlinear, hdegree, hconst, hInvDegree, hInvZero, hleft, hright,
      hforbidden, hmodelZero, hmodelLinear, hallowed, hauto, hmodelDegree, hmodelInvDegree,
      hjac, hconjugacy, hnorm⟩ := hQ.2 k hk
    exact ⟨hconst, isConstantVolumeJet_inverseJet hd hconst hInvZero hInvDegree hleft,
      hlinear, hleft, hright⟩
  · obtain ⟨hcorrection, hinverse⟩ := hQ.1 k hk
    rw [hcorrection, hinverse]
    exact ⟨hid, hid, id_linearPart, by simpa only [comp_id] using jetEq_refl (PolyMap.id : PolyMap n) d,
      by simpa only [comp_id] using jetEq_refl (PolyMap.id : PolyMap n) d⟩

end Yau.Proofs.Y01Aux
