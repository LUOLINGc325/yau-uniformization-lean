import Yau.LeafProofs.L05PerturbationSeries
import Yau.LeafProofs.L05PerturbationRescaledData

open Filter Set Metric
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_sym_completeSpace (n : ℕ) : CompleteSpace (Sym n) := by
  have hClosed : IsClosed {A : Mat n | IsSelfAdjoint A} :=
    isClosed_eq continuous_star continuous_id
  exact hClosed.isComplete.completeSpace_coe

theorem perturb_polynomial_coefficient_limits {n : ℕ} {rho eta K : ℝ}
    (hr : 0 < rho) (hr1 : rho < 1) (he : 0 < eta)
    (c q : ℕ → ℝ) (b : ℕ → Space n →L[ℝ] ℝ) (A : ℕ → Sym n)
    (hc0 : c 0=0) (hb0 : b 0=0) (hA0 : A 0=0) (hq0 : q 0=0)
    (hc : ∀ k : ℕ, |c (k+1)-c k| ≤ K*(rho^k : ℝ)^(2+eta))
    (hb : ∀ k : ℕ, ‖b (k+1)-b k‖ ≤ K*(rho^k : ℝ)^(1+eta))
    (hA : ∀ k : ℕ, ‖A (k+1)-A k‖ ≤ K*(rho^k : ℝ)^eta)
    (hq : ∀ k : ℕ, |q (k+1)-q k| ≤ K*(rho^k : ℝ)^eta) :
    ∃ (cInf qInf : ℝ) (bInf : Space n →L[ℝ] ℝ) (AInf : Sym n),
      Tendsto c atTop (𝓝 cInf) ∧ Tendsto b atTop (𝓝 bInf) ∧
      Tendsto A atTop (𝓝 AInf) ∧ Tendsto q atTop (𝓝 qInf) ∧
      |cInf| ≤ K/(1-rho^(2+eta)) ∧ ‖bInf‖ ≤ K/(1-rho^(1+eta)) ∧
      ‖AInf‖ ≤ K/(1-rho^eta) ∧ |qInf| ≤ K/(1-rho^eta) ∧
      (∀ k : ℕ, |cInf-c k| ≤ (K/(1-rho^(2+eta)))*(rho^k : ℝ)^(2+eta)) ∧
      (∀ k : ℕ, ‖bInf-b k‖ ≤ (K/(1-rho^(1+eta)))*(rho^k : ℝ)^(1+eta)) ∧
      (∀ k : ℕ, ‖AInf-A k‖ ≤ (K/(1-rho^eta))*(rho^k : ℝ)^eta) ∧
      (∀ k : ℕ, |qInf-q k| ≤ (K/(1-rho^eta))*(rho^k : ℝ)^eta) := by
  obtain ⟨cInf,hcLim,hcNorm,hcTail⟩ := perturb_rpow_geometric_limit hr hr1 (show 0 < 2+eta by linarith)
    c hc0 (by simpa only [Real.norm_eq_abs] using hc)
  obtain ⟨bInf,hbLim,hbNorm,hbTail⟩ := perturb_rpow_geometric_limit hr hr1 (show 0 < 1+eta by linarith) b hb0 hb
  obtain ⟨AInf,hALim,hANorm,hATail⟩ := @perturb_rpow_geometric_limit (Sym n) inferInstance (perturb_sym_completeSpace n) rho eta K hr hr1 he A hA0 hA
  obtain ⟨qInf,hqLim,hqNorm,hqTail⟩ := perturb_rpow_geometric_limit hr hr1 he q hq0
    (by simpa only [Real.norm_eq_abs] using hq)
  exact ⟨cInf,qInf,bInf,AInf,hcLim,hbLim,hALim,hqLim,
    by simpa only [Real.norm_eq_abs] using hcNorm,hbNorm,hANorm,
    by simpa only [Real.norm_eq_abs] using hqNorm,
    by simpa only [Real.norm_eq_abs] using hcTail,hbTail,hATail,
    by simpa only [Real.norm_eq_abs] using hqTail⟩

theorem perturb_polynomial_limit_compatibility {n : ℕ}
    (Phi : Sym n → Point n → ℝ) (f : Point n → ℝ)
    (hC : ContinuousOn (fun z : Sym n × Point n => Phi z.1 z.2) (univ ×ˢ backward 1))
    (A : ℕ → Sym n) (q : ℕ → ℝ) (AInf : Sym n) (qInf : ℝ)
    (hALim : Tendsto A atTop (𝓝 AInf)) (hqLim : Tendsto q atTop (𝓝 qInf))
    (hCompat : ∀ k, q k=Phi (A k) (0,0)+f (0,0)) : qInf=Phi AInf (0,0)+f (0,0) := by
  have hPoint : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hPhiOn : ContinuousOn (fun H : Sym n => Phi H (0,0)) univ :=
    hC.comp (continuous_id.prodMk continuous_const).continuousOn (by intro H _; exact ⟨mem_univ _,hPoint⟩)
  have hPhi : Continuous (fun H : Sym n => Phi H (0,0)) := continuousOn_univ.mp hPhiOn
  have hLim := ((hPhi.tendsto AInf).comp hALim).add_const (f (0,0))
  apply tendsto_nhds_unique hqLim
  convert hLim using 1
  exact funext hCompat

end Yau.LeafProofs.L05Aux
