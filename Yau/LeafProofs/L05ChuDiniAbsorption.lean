import Yau.LeafProofs.L05DiniKernelOscillation

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05ChuDiniAbsorptionDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuDiniAbsorptionDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuDiniAbsorptionHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05ChuDiniAbsorptionHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem chu_dini_source_absorption {phi psi : ℝ → ℝ} {eta gamma Bphi Bpsi C epsilon A G : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hg : 0 < gamma) (hg1 : gamma < 1)
    (hBp : 0 ≤ Bphi) (hBs : 0 ≤ Bpsi) (hC : 0 < C) (heps : 0 ≤ epsilon)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hmp : Measurable phi) (hms : Measurable psi)
    (hpp : powerBound eta Bphi phi) (hps : powerBound eta Bpsi psi)
    (hSource : ∀ r ∈ Set.Ioc (0:ℝ) 1, psi r ≤ epsilon*phi r+A*r^gamma)
    (hKernel : ∀ r ∈ Set.Ioc (0:ℝ) 1, phi r ≤ C*(diniTransform psi r+r*G))
    (hSmallGamma : (C*epsilon)*diniPowerConstant gamma ≤ 1/2)
    (hSmallEta : (C*epsilon)*diniPowerConstant eta ≤ 1/2) :
    powerBound gamma (2*(C*(A*diniPowerConstant gamma+G))) phi := by
  have hk : 0 ≤ diniPowerConstant gamma := by unfold diniPowerConstant; positivity
  apply dini_iteration he he1 hg hg1 (mul_nonneg hC.le (add_nonneg (mul_nonneg hA hk) hG))
    hBp (mul_nonneg hC.le heps) hmp hpp _ hSmallGamma hSmallEta
  intro r hr
  have hIp := diniIntegrable_of_powerBound he he1 hBp hmp hpp hr.1 hr.2
  have hIs := diniIntegrable_of_powerBound he he1 hBs hms hps hr.1 hr.2
  have hu : 0 ≤ min (2*r) 1 := le_min (by linarith only [hr.1]) zero_le_one
  have hIg : diniIntegrable (fun a : ℝ => a^gamma) r :=
    ⟨diniPower_near_integrable hg hg1 hu,diniPower_far_integrable hg1 hr.1 hr.2⟩
  have hEp := diniIntegrable_const_mul hIp epsilon
  have hAg := diniIntegrable_const_mul hIg A
  have hTrans := diniTransform_mono hr.1 hr.2 hIs (diniIntegrable_add hEp hAg) hSource
  rw [diniTransform_add hEp hAg,diniTransform_const_mul,diniTransform_const_mul] at hTrans
  have hPower := mul_le_mul_of_nonneg_left (diniTransform_power_le hg hg1 hr.1 hr.2) hA
  have hrPow : r ≤ r^gamma := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 hg1.le
  have hRG := mul_le_mul_of_nonneg_right hrPow hG
  have hb := mul_le_mul_of_nonneg_left (add_le_add_right hTrans (r*G)) hC.le
  have hpScaled := mul_le_mul_of_nonneg_left hPower hC.le
  have hgScaled := mul_le_mul_of_nonneg_left hRG hC.le
  nlinarith only [hKernel r hr,hb,hpScaled,hgScaled]

theorem constant_causal_sharp_oscillation (n : ℕ) (hn : 0 < n) (ell L : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Mat n) (T eta gamma G F W MH epsilon A : ℝ) (g w : Point n → ℝ),
      0 < T → T ≤ 1 → 0 < eta → eta < 1 → 0 < gamma → gamma < 1 →
      0 ≤ G → 0 ≤ F → 0 ≤ W → 0 ≤ epsilon → 0 ≤ A →
      Elliptic (cylinder Set.univ 0 T) (fun _ => a) ell L →
      HolderBound eta (cylinder Set.univ 0 T) g F →
      (∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G) → (∀ x : Space n, g (x,0)=0) →
      C2 (cylinder Set.univ 0 T) w → (∀ p ∈ cylinder Set.univ 0 T, |w p| ≤ W) →
      (∀ x : Space n, w (x,0)=0) →
      (∀ p ∈ Set.univ ×ˢ Set.Ioc (0:ℝ) T,
        linearOp (cylinder Set.univ 0 T) (fun _ => a) (fun _ _ => 0) w p=g p) →
      HolderBound eta (cylinder Set.univ 0 T) (spatialDD w) MH →
      (∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        |g p-g q| ≤ epsilon*‖spatialDD w p-spatialDD w q‖+A*holderWeight gamma p q) →
      (C*epsilon)*diniPowerConstant gamma ≤ 1/2 →
      (C*epsilon)*diniPowerConstant eta ≤ 1/2 →
      powerBound gamma (2*(C*((2*A)*diniPowerConstant gamma+G)))
        (chuOscillation (cylinder Set.univ 0 T) (spatialDD w)) := by
  obtain ⟨C,hC,hKernel⟩ := constant_causal_dini_oscillation n hn ell L hell hL
  refine ⟨C,hC,?_⟩
  intro a T eta gamma G F W MH epsilon A g w hT hT1 he he1 hg hg1 hG0 hF hW heps hA hEll
    hgf hG hg0 hw hwB hw0 hPDE hH hpair hSmallGamma hSmallEta
  have hSource (r : ℝ) (hr : r ∈ Set.Ioc (0:ℝ) 1) :
      chuOscillation (cylinder Set.univ 0 T) g r ≤
        epsilon*chuOscillation (cylinder Set.univ 0 T) (spatialDD w) r+(2*A)*r^gamma := by
    apply chuOscillation_perturbation (g := g) (J := spatialDD w) (A := 2*A) (gamma := gamma) heps (by positivity) hH.1 hr.1.le hH.2.1
    intro p hp q hq hpq
    have hWeight := mul_le_mul_of_nonneg_left (holderWeight_le_twice_radius_power hg.le hpq) hA
    have hScaled := add_le_add_left hWeight (epsilon*‖spatialDD w p-spatialDD w q‖)
    change |g p-g q| ≤ epsilon*‖spatialDD w p-spatialDD w q‖+(2*A)*r^gamma
    calc
      _ ≤ epsilon*‖spatialDD w p-spatialDD w q‖+A*holderWeight gamma p q := hpair p hp q hq
      _ ≤ A*(2*r^gamma)+epsilon*‖spatialDD w p-spatialDD w q‖ := by linarith only [hScaled]
      _ = _ := by ring
  exact chu_dini_source_absorption (Bphi := 2*MH) (Bpsi := 2*F) he he1 hg hg1
    (mul_nonneg (by norm_num) hH.1) (mul_nonneg (by norm_num) hgf.1) hC heps
    (by positivity) hG0 (chuOscillation_measurable hH.1 hH.2.1)
    (chuOscillation_measurable hgf.1 hgf.2.1) (chuOscillation_powerBound he.le hH)
    (chuOscillation_powerBound he.le hgf) hSource
    (hKernel a T eta G F W g w hT hT1 he he1 hG0 hF hW hEll hgf hG hg0 hw hwB hw0 hPDE)
    hSmallGamma hSmallEta

end Yau.LeafProofs.L05Aux
