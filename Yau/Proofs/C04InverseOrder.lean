import Yau.Proofs.C04Scaling

/-! Positive metric matrix inversion reverses the genuine Loewner order. -/

noncomputable section
open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem matrix_inverse_order (H G : Herm n) (hH : H.PosDef) (hG : G.PosDef)
    (hHG : HermLE H G) : HermLE G⁻¹ H⁻¹ := by
  let U := hH.isUnit.unit
  let V := hG.isUnit.unit
  have hU : (U : Herm n) = H := hH.isUnit.unit_spec
  have hV : (V : Herm n) = G := hG.isUnit.unit_spec
  have ha : (0 : Herm n) ≤ (U : Herm n) := by rw [hU]; exact hH.posSemidef.nonneg
  have hab : (U : Herm n) ≤ (V : Herm n) := by
    rw [hU, hV]
    exact sub_nonneg.mp hHG.nonneg
  have hh := CStarAlgebra.inv_le_inv ha hab
  have hUi : (↑U⁻¹ : Herm n) = H⁻¹ := by
    calc
      (↑U⁻¹ : Herm n) = Ring.inverse (U : Herm n) := (Ring.inverse_unit U).symm
      _ = Ring.inverse H := congrArg Ring.inverse hU
      _ = H⁻¹ := (Matrix.nonsing_inv_eq_ringInverse H).symm
  have hVi : (↑V⁻¹ : Herm n) = G⁻¹ := by
    calc
      (↑V⁻¹ : Herm n) = Ring.inverse (V : Herm n) := (Ring.inverse_unit V).symm
      _ = Ring.inverse G := congrArg Ring.inverse hV
      _ = G⁻¹ := (Matrix.nonsing_inv_eq_ringInverse G).symm
  rw [hUi, hVi] at hh
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hh)

theorem inverse_order_of_real_upper (H G : Herm n) (hH : H.PosDef) (hG : G.PosDef)
    (c : ℝ) (hc : 0 < c) (hHG : HermLE H ((c : ℂ) • G)) :
    HermLE ((c⁻¹ : ℂ) • G⁻¹) H⁻¹ := by
  have hcC : (0 : ℂ) < (c : ℂ) := Complex.pos_iff.mpr ⟨hc, by rw [Complex.ofReal_im]⟩
  have hcg : ((c : ℂ) • G).PosDef := hG.smul hcC
  have hh := matrix_inverse_order H ((c : ℂ) • G) hH hcg hHG
  rwa [inverse_real_smul c hc G hG] at hh

end Yau.Proofs.C04Aux
