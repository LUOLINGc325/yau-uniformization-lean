import spec.CHAIN.CONTRACTS
import Yau.Proofs.Y02Algebra
import Yau.Proofs.Y02One
import Yau.Proofs.Y02Estimates
import Yau.Proofs.Y02Realization

/-! Realization of constant-volume jets. -/

noncomputable section

namespace Yau.Proofs

open Yau.Blueprint Yau.BlueprintContracts

/-- The zero-dimensional case has a unique polynomial map. -/
theorem Y02_zero (d : ℕ) : VolumeJets 0 d := by
  refine ⟨0, 0, ?_⟩
  intro J hJ
  refine ⟨PolyMap.id, PolyMap.id, Y02Aux.automorphism_id, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · simp [PolyMap.degree]
  · simp [PolyMap.degree]
  · simp [PolyMap.coeffNorm]

/-- In dimension one, the Jacobian condition kills all nonlinear jet coefficients. -/
theorem Y02_one (d : ℕ) : VolumeJets 1 d := by
  refine ⟨1, 1, ?_⟩
  intro J hJ
  let a : ℂ := (J 0).coeff (Finsupp.single 0 1)
  have hlin : J = Y02Aux.scalarMap a := Y02Aux.volumeJet_one_linear J hJ
  have ha : a ≠ 0 := by
    have h := hJ.2.2.1
    have heq : J.linearPart.det = a := Matrix.det_fin_one _
    rwa [heq] at h
  refine ⟨J, Y02Aux.scalarMap a⁻¹, ?_, Y02Aux.jetEq_refl J d, ?_,
    Y02Aux.scalarMap_degree_le _, ?_⟩
  · rw [hlin]
    exact Y02Aux.scalarMap_automorphism ha
  · rw [hlin]
    exact Y02Aux.scalarMap_degree_le _
  · have hentry := Y02Aux.norm_entry_le_matOpNorm J.linearPart⁻¹ 0 0
    have hinv : J.linearPart⁻¹ = (Y02Aux.scalarMap a⁻¹).linearPart := by
      rw [hlin]
      exact Y02Aux.scalarMap_linearPart_inv ha
    have hinvcoef : J.linearPart⁻¹ 0 0 = a⁻¹ := by
      rw [hinv, Y02Aux.scalarMap_linearPart]
    rw [hinvcoef] at hentry
    rw [Y02Aux.scalarMap_coeffNorm, Real.rpow_one, one_mul]
    linarith

/-- The paper's volume-jet realization theorem in every finite dimension. -/
theorem Y02 : Y02_contract := by
  intro n d hd
  exact Y02Aux.volumeJets_proved n d hd

end Yau.Proofs
