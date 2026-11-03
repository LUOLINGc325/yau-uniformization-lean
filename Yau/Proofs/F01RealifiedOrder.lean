import Yau.Proofs.F01TransformedMatrixIdentity

/-! The frozen realification preserves actual positive-semidefinite
Hermitian inequalities. These are bounds for the transformed Hessian. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem rawReal_posSemidef {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef) :
    (G01Aux.rawReal H).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact G01Aux.rawReal_isSymm H hH.isHermitian
  · intro r
    have hp := Yau.LeafProofs.L12Aux.hermitianRealification_quadratic_nonneg H hH r
    rw [G01Aux.hermitianRealification_eq, Matrix.smul_mulVec, dotProduct_smul] at hp
    change 0 ≤ 2 * (star r ⬝ᵥ (G01Aux.rawReal H *ᵥ r)) at hp
    linarith

theorem iota_posSemidef {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef) :
    ((iota H : Sym n) : Mat n).PosSemidef := by
  rw [← G01Aux.rawReal_eq_iota H hH.isHermitian]
  exact rawReal_posSemidef hH

theorem iota_one_matrix : ((iota (1 : Matrix (Fin n) (Fin n) ℂ) : Sym n) : Mat n) = 1 := by
  rw [← G01Aux.rawReal_eq_iota _ Matrix.isHermitian_one]
  exact G01Aux.rawReal_one

theorem iota_upper_order {H K : Matrix (Fin n) (Fin n) ℂ} {C : ℝ}
    (hupper : ((C : ℂ) • H - K).PosSemidef) :
    (C • (iota H : Mat n) - (iota K : Mat n)).PosSemidef := by
  have hp := iota_posSemidef hupper
  rw [iota_sub, iota_real_smul] at hp
  exact hp

theorem iota_lower_order {H K : Matrix (Fin n) (Fin n) ℂ} {c : ℝ}
    (hlower : (K - (c : ℂ) • H).PosSemidef) :
    ((iota K : Mat n) - c • (iota H : Mat n)).PosSemidef := by
  have hp := iota_posSemidef hlower
  rw [iota_sub, iota_real_smul] at hp
  exact hp

end Yau.NodeProofs.F01Aux
