import Yau.LeafProofs.L17LocalizedSchauderTwoJets

open Set Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def unitValue (ρ : ℝ) (v : E → F) (z : E) : F := (ρ^2)⁻¹ • v (ρ • z)
def unitFirstJet (ρ : ℝ) (D : E → E →L[ℝ] F) (z : E) : E →L[ℝ] F := ρ⁻¹ • D (ρ • z)

theorem unitValue_hasFDerivAt {ρ : ℝ} (hρ : 0 < ρ) (v : E → F) (D : E → E →L[ℝ] F) (z : E)
    (hv : HasFDerivAt v (D (ρ • z)) (ρ • z)) :
    HasFDerivAt (unitValue ρ v) (unitFirstJet ρ D z) z := by
  let L : E →L[ℝ] E := ρ • ContinuousLinearMap.id ℝ E
  have h : HasFDerivAt (unitValue ρ v) ((ρ^2)⁻¹ • ((D (ρ • z)).comp L)) z :=
    (hv.comp z L.hasFDerivAt).const_smul ((ρ^2)⁻¹)
  have hEq : (ρ^2)⁻¹ • ((D (ρ • z)).comp L) = unitFirstJet ρ D z := by
    ext w
    simp only [unitFirstJet,L,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_smul]
    have he : (ρ^2)⁻¹*ρ = ρ⁻¹ := by field_simp [hρ.ne']
    rw [he]
  rwa [hEq] at h

theorem unitFirstJet_hasFDerivAt {ρ : ℝ} (hρ : 0 < ρ)
    (D : E → E →L[ℝ] F) (H : E → E →L[ℝ] E →L[ℝ] F) (z : E)
    (hD : HasFDerivAt D (H (ρ • z)) (ρ • z)) :
    HasFDerivAt (unitFirstJet ρ D) (H (ρ • z)) z := by
  let L : E →L[ℝ] E := ρ • ContinuousLinearMap.id ℝ E
  have h : HasFDerivAt (unitFirstJet ρ D) (ρ⁻¹ • ((H (ρ • z)).comp L)) z :=
    (hD.comp z L.hasFDerivAt).const_smul (ρ⁻¹)
  have hEq : ρ⁻¹ • ((H (ρ • z)).comp L) = H (ρ • z) := by
    ext w
    simp only [L,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_smul,inv_mul_cancel₀ hρ.ne',one_smul]
  rwa [hEq] at h

theorem norm_inv_smul_le_of_le {r C : ℝ} (hr : 0 < r) (v : F) (hv : ‖v‖ ≤ r*C) :
    ‖r⁻¹ • v‖ ≤ C := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ r⁻¹*(r*C) := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hr.le)
    _ = C := by rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]

theorem unitValue_norm_le {ρ C : ℝ} (hρ : 0 < ρ) (v : E → F) (z : E)
    (hv : ‖v (ρ • z)‖ ≤ ρ^2*C) : ‖unitValue ρ v z‖ ≤ C :=
  norm_inv_smul_le_of_le (sq_pos_of_pos hρ) _ hv

theorem unitFirstJet_norm_le {ρ C : ℝ} (hρ : 0 < ρ) (D : E → E →L[ℝ] F) (z : E)
    (hD : ‖D (ρ • z)‖ ≤ ρ*C) : ‖unitFirstJet ρ D z‖ ≤ C :=
  norm_inv_smul_le_of_le hρ _ hD

theorem unitValue_sub_norm_le {ρ C : ℝ} (hρ : 0 < ρ) (v w : E → F) (z y : E)
    (hv : ‖v (ρ • z)-w (ρ • y)‖ ≤ ρ^2*C) :
    ‖unitValue ρ v z-unitValue ρ w y‖ ≤ C := by
  change ‖(ρ^2)⁻¹ • v (ρ • z)-(ρ^2)⁻¹ • w (ρ • y)‖ ≤ C
  rw [← smul_sub]
  exact norm_inv_smul_le_of_le (sq_pos_of_pos hρ) _ hv

theorem unitFirstJet_sub_norm_le {ρ C : ℝ} (hρ : 0 < ρ)
    (D J : E → E →L[ℝ] F) (z y : E) (hD : ‖D (ρ • z)-J (ρ • y)‖ ≤ ρ*C) :
    ‖unitFirstJet ρ D z-unitFirstJet ρ J y‖ ≤ C := by
  change ‖ρ⁻¹ • D (ρ • z)-ρ⁻¹ • J (ρ • y)‖ ≤ C
  rw [← smul_sub]
  exact norm_inv_smul_le_of_le hρ _ hD

end Yau.LeafProofs.L17LocalizedSchauderAux
