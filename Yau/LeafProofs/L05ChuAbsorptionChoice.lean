import Yau.LeafProofs.L05ChuSlabSharp

noncomputable section

namespace Yau.LeafProofs.L05Aux

theorem chu_numeric_absorption_choice {C eta gamma : ℝ} (hC : 0 < C)
    (he : 0 < eta) (he1 : eta < 1) (hg : 0 < gamma) (hg1 : gamma < 1) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      (C*epsilon)*diniPowerConstant eta ≤ 1/2 ∧ (C*epsilon)*diniPowerConstant gamma ≤ 1/2 := by
  have hkE : 0 ≤ diniPowerConstant eta := by unfold diniPowerConstant; positivity
  have hkG : 0 ≤ diniPowerConstant gamma := by unfold diniPowerConstant; positivity
  let D : ℝ := 4*(1+C)*(1+diniPowerConstant eta+diniPowerConstant gamma)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD1 : 1 ≤ D := by
    have hmul := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 1+diniPowerConstant eta+diniPowerConstant gamma by linarith only [hkE,hkG])
      (show 0 ≤ 1+C by positivity)
    dsimp only [D]
    nlinarith only [hmul,hC]
  have hED : 2*C*diniPowerConstant eta ≤ D := by
    dsimp only [D]
    nlinarith only [hkE,hkG,hC,mul_nonneg hC.le hkE,mul_nonneg hC.le hkG]
  have hGD : 2*C*diniPowerConstant gamma ≤ D := by
    dsimp only [D]
    nlinarith only [hkE,hkG,hC,mul_nonneg hC.le hkE,mul_nonneg hC.le hkG]
  refine ⟨D⁻¹,inv_pos.mpr hD,(inv_le_one₀ hD).mpr hD1,?_,?_⟩
  · apply le_of_mul_le_mul_right (a := D) (a0 := hD)
    have hCancel : ((C*D⁻¹)*diniPowerConstant eta)*D=C*diniPowerConstant eta := by
      field_simp [hD.ne']
    rw [hCancel]
    linarith only [hED]
  · apply le_of_mul_le_mul_right (a := D) (a0 := hD)
    have hCancel : ((C*D⁻¹)*diniPowerConstant gamma)*D=C*diniPowerConstant gamma := by
      field_simp [hD.ne']
    rw [hCancel]
    linarith only [hGD]

end Yau.LeafProofs.L05Aux
