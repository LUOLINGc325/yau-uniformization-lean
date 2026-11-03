import Yau.LeafProofs.L05PerturbationPowers

open Set
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L05Aux

theorem perturb_positive_power_threshold {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ r ≤ a ∧ r^p ≤ b := by
  let r := min a (b^(p⁻¹))
  have hr : 0 < r := lt_min ha (Real.rpow_pos_of_pos hb _)
  exact ⟨r,hr,min_le_left _ _,(Real.le_rpow_inv_iff_of_pos hr.le hb.le hp).mp (min_le_right _ _)⟩

theorem perturb_improvement_parameters {sigma alpha beta nu Cc Cp K : ℝ}
    (hs : 0 < sigma) (ha : 0 < alpha) (hb : 0 < beta) (hn : 0 < nu)
    (hCc : 0 < Cc) (hCp : 0 < Cp) (hK : 0 < K) :
    ∃ eta rho tau delta : ℝ,
      0 < eta ∧ eta < min alpha beta ∧ eta < sigma ∧
      0 < rho ∧ rho ≤ 1/16 ∧ 0 < tau ∧ tau ≤ 1/8 ∧ 0 < delta ∧ delta ≤ 1 ∧
      3*K*rho^(sigma-eta) ≤ 1/2 ∧
      Cc*tau^nu ≤ rho^(2+eta)/4 ∧
      Cp*delta*(1+tau^(-2 : ℝ)) ≤ rho^(2+eta)/4 := by
  let eta := min sigma (min alpha beta)/2
  have hMin : 0 < min sigma (min alpha beta) := lt_min hs (lt_min ha hb)
  have he : 0 < eta := by dsimp only [eta]; positivity
  have heAB : eta < min alpha beta := by
    dsimp only [eta]
    linarith only [hMin,min_le_right sigma (min alpha beta)]
  have heS : eta < sigma := by
    dsimp only [eta]
    linarith only [hMin,min_le_left sigma (min alpha beta)]
  have hDiff : 0 < sigma-eta := sub_pos.mpr heS
  obtain ⟨rho,hr,hrb,hrPower⟩ := perturb_positive_power_threshold
    (by norm_num : (0 : ℝ) < 1/16) (by positivity : 0 < 1/(6*K)) hDiff
  let eps := rho^(2+eta)
  have hEps : 0 < eps := Real.rpow_pos_of_pos hr _
  obtain ⟨tau,ht,htb,htPower⟩ := perturb_positive_power_threshold
    (by norm_num : (0 : ℝ) < 1/16) (div_pos hEps (by positivity : 0 < 4*Cc)) hn
  let delta := min 1 (eps/(4*Cp*(1+tau^(-2 : ℝ))))
  have hDen : 0 < 4*Cp*(1+tau^(-2 : ℝ)) := by positivity
  have hd : 0 < delta := lt_min zero_lt_one (div_pos hEps hDen)
  have hSmallR : 3*K*rho^(sigma-eta) ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6*K)).mp hrPower
    nlinarith only [hh]
  have hSmallT : Cc*tau^nu ≤ eps/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*Cc)).mp htPower
    nlinarith only [hh]
  have hSmallD : Cp*delta*(1+tau^(-2 : ℝ)) ≤ eps/4 := by
    have hh := (le_div_iff₀ hDen).mp (min_le_right 1 (eps/(4*Cp*(1+tau^(-2 : ℝ)))))
    change delta*(4*Cp*(1+tau^(-2 : ℝ))) ≤ eps at hh
    nlinarith only [hh]
  exact ⟨eta,rho,tau,delta,he,heAB,heS,hr,hrb,ht,by linarith only [htb],hd,
    min_le_left _ _,hSmallR,hSmallT,hSmallD⟩

end Yau.LeafProofs.L05Aux
