import Yau.Proofs.Y01InverseJets

/-! After the correction's volume has been proved, the original Y02
realization supplies a bounded inverse jet, with both inverse identities. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux

variable {n d : ℕ}

theorem inverse_fixesZero_of_automorphism {R S : PolyMap n}
    (hR : R.FixesZero) (hAuto : IsPolyAutomorphism R S) : S.FixesZero := by
  have hId0 : (PolyMap.id : PolyMap n).eval 0 = 0 := by
    apply (fixesZero_iff_eval_zero _).mp
    intro i
    simp [PolyMap.id, coeff_X]
  have h := congrArg (fun P : PolyMap n => P.eval 0) hAuto.2
  rw [polyMap_eval_comp, (fixesZero_iff_eval_zero R).mp hR, hId0] at h
  exact (fixesZero_iff_eval_zero S).mpr h

theorem inverseJet_of_realization (H R S : PolyMap n) (hH : H.FixesZero)
    (hAuto : IsPolyAutomorphism R S) (hJet : PolyMap.JetEq R H d) :
    let I := truncate d S
    I.degree ≤ d ∧ I.FixesZero ∧
      PolyMap.JetEq (H.comp I) PolyMap.id d ∧ PolyMap.JetEq (I.comp H) PolyMap.id d ∧
      I.coeffNorm ≤ S.coeffNorm := by
  have hR : R.FixesZero := jetEq_fixesZero hJet hH
  have hS : S.FixesZero := inverse_fixesZero_of_automorphism hR hAuto
  have hI : (truncate d S).FixesZero := truncate_fixesZero hS
  refine ⟨truncate_degree_le d S, hI, ?_, ?_, truncate_coeffNorm_le d S⟩
  · have h := Yau.Proofs.Y01Aux.jetEq_comp (fun i β hβ => (hJet i β hβ).symm)
      (truncate_jetEq d S) hI
    rw [hAuto.1] at h
    exact h
  · have h := Yau.Proofs.Y01Aux.jetEq_comp (truncate_jetEq d S)
      (fun i β hβ => (hJet i β hβ).symm) hH
    rw [hAuto.2] at h
    exact h

theorem inverseJet_of_volumeJets {Dd : ℕ} {C : ℝ}
    (hrealize : ∀ P : PolyMap n, IsConstantVolumeJet P d →
      ∃ R S : PolyMap n, IsPolyAutomorphism R S ∧ PolyMap.JetEq R P d ∧
        R.degree ≤ Dd ∧ S.degree ≤ Dd ∧
        R.coeffNorm + S.coeffNorm ≤ C * (1 + P.coeffNorm + matOpNorm P.linearPart⁻¹) ^ C)
    (H : PolyMap n) (hH : IsConstantVolumeJet H d) :
    ∃ I : PolyMap n, I.degree ≤ d ∧ I.FixesZero ∧
      PolyMap.JetEq (H.comp I) PolyMap.id d ∧ PolyMap.JetEq (I.comp H) PolyMap.id d ∧
      I.coeffNorm ≤ C * (1 + H.coeffNorm + matOpNorm H.linearPart⁻¹) ^ C := by
  obtain ⟨R, S, hAuto, hJet, hRdegree, hSdegree, hNorm⟩ := hrealize H hH
  obtain ⟨hdegree, hzero, hleft, hright, hbound⟩ := inverseJet_of_realization H R S hH.1 hAuto hJet
  refine ⟨truncate d S, hdegree, hzero, hleft, hright, ?_⟩
  exact hbound.trans ((by linarith [coeffNorm_nonneg R] : S.coeffNorm ≤ R.coeffNorm + S.coeffNorm).trans hNorm)

end Yau.Proofs.Y06Aux
