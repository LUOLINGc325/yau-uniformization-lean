import Yau.Proofs.P06SpectralRegularization

noncomputable section
open ContinuousLinearMap
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux.Spectral
open Yau.LeafProofs.L19Aux ComplexHilbert

/-- The actual generator multiplier has its global positive-time bound,
including spectral zero and the kernel endpoint. -/
theorem heatEnergyMultiplier_bound {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖scalarHeatInverseMultiplier t s - scalarHeatMultiplier t s‖ ≤ t⁻¹ := by
  by_cases hspos : 0 < s
  · let a : ℝ := s⁻¹ - 1
    have ha : 0 ≤ a := sub_nonneg.mpr ((one_le_inv₀ hspos).mpr hs.2)
    have heq : scalarHeatInverseMultiplier t s - scalarHeatMultiplier t s =
        a * Real.exp (-t * a) := by
      rw [scalarHeatInverseMultiplier, scalarHeatMultiplier_of_pos t hspos]
      dsimp only [a]
      rw [div_eq_mul_inv]
      ring
    rw [heq, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ha (Real.exp_pos _).le)]
    have hb := (Real.mul_exp_neg_le_exp_neg_one (t * a)).trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
    have hb' : (a * Real.exp (-t * a)) * t ≤ 1 := by
      simpa only [neg_mul, mul_assoc, mul_left_comm, mul_comm] using hb
    simpa only [one_div] using (le_div_iff₀ ht).mpr hb'
  · have hz : s = 0 := le_antisymm (le_of_not_gt hspos) hs.1
    simp only [hz, scalarHeatInverseMultiplier_zero, scalarHeatMultiplier_zero,
      sub_self, norm_zero]
    exact inv_nonneg.mpr ht.le

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
  (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R)

theorem complexHeatEnergy_opNorm_le {t : ℝ} (ht : 0 < t) :
    ‖complexHeatInverse R hRs hRp hRb hRi t - complexHeat R hRs hRp hRb hRi t‖ ≤ t⁻¹ := by
  rw [complexHeatInverse, complexHeat_of_pos R hRs hRp hRb hRi ht,
    ← cfc_sub (f := scalarHeatInverseMultiplier t) (g := scalarHeatMultiplier t)
      (a := complexResolvent R hRs hRp hRb hRi)
      (scalarHeatInverseMultiplier_continuous ht).continuousOn
      (scalarHeatMultiplier_continuous ht).continuousOn]
  apply norm_cfc_le (inv_nonneg.mpr ht.le)
  intro s hs
  exact heatEnergyMultiplier_bound ht (complexResolvent_spectrum R hRs hRp hRb hRi hs)

theorem realHeatEnergy_norm_le {t : ℝ} (ht : 0 < t) (x : H) :
    ‖realHeatInverse R hRs hRp hRb hRi t x - realHeat R hRs hRp hRb hRi t x‖ ≤ t⁻¹ * ‖x‖ := by
  rw [← ComplexHilbert.ofReal_norm, map_sub,
    realHeatInverse_ofReal R hRs hRp hRb hRi ht, realHeat_ofReal]
  calc
    _ = ‖(complexHeatInverse R hRs hRp hRb hRi t - complexHeat R hRs hRp hRb hRi t)
        (ofRealCLM x)‖ := by rw [sub_apply]
    _ ≤ ‖complexHeatInverse R hRs hRp hRb hRi t - complexHeat R hRs hRp hRb hRi t‖ *
        ‖(ofRealCLM x : ComplexHilbert H)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ t⁻¹ * ‖x‖ := by
      rw [ComplexHilbert.ofReal_norm]
      exact mul_le_mul_of_nonneg_right (complexHeatEnergy_opNorm_le R hRs hRp hRb hRi ht)
        (norm_nonneg x)

theorem realHeatInverse_norm_le {t : ℝ} (ht : 0 < t) (x : H) :
    ‖realHeatInverse R hRs hRp hRb hRi t x‖ ≤ (1 + t⁻¹) * ‖x‖ := by
  have he : realHeatInverse R hRs hRp hRb hRi t x =
      (realHeatInverse R hRs hRp hRb hRi t x - realHeat R hRs hRp hRb hRi t x) +
        realHeat R hRs hRp hRb hRi t x := by abel
  conv_lhs => rw [he]
  exact (norm_add_le _ _).trans (by
    have h₁ := realHeatEnergy_norm_le R hRs hRp hRb hRi ht x
    have h₂ := realHeat_norm_le R hRs hRp hRb hRi t x
    nlinarith)

theorem realHeat_commute_energy {t : ℝ} (ht : 0 < t) :
    Commute (realHeat R hRs hRp hRb hRi t)
      (realHeatInverse R hRs hRp hRb hRi t - realHeat R hRs hRp hRb hRi t) := by
  have hSB : Commute (realHeat R hRs hRp hRb hRi t)
      (realHeatInverse R hRs hRp hRb hRi t) := by
    rw [realHeat_factor R hRs hRp hRb hRi ht]
    exact (realHeatInverse_commute_resolvent R hRs hRp hRb hRi t).symm.mul_left (Commute.refl _)
  exact hSB.sub_right (Commute.refl _)

end Yau.NodeProofs.P06Aux.Spectral
