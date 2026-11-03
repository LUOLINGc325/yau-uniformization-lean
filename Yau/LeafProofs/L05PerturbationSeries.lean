import Yau.LeafProofs.L05PerturbationPowers
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L05Aux

theorem perturb_geometric_limit {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {t K : ℝ} (ht : t < 1) (v : ℕ → V)
    (hInc : ∀ k, ‖v (k+1)-v k‖ ≤ K*t^k) :
    ∃ vInf : V, Tendsto v atTop (𝓝 vInf) ∧
      ∀ k, ‖vInf-v k‖ ≤ (K/(1-t))*t^k := by
  have hDist : ∀ k, dist (v k) (v (k+1)) ≤ K*t^k := by
    intro k
    simpa only [dist_eq_norm'] using hInc k
  obtain ⟨vInf,hLim⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric t K ht hDist)
  refine ⟨vInf,hLim,?_⟩
  intro k
  have hBound := dist_le_of_le_geometric_of_tendsto t K ht hDist hLim k
  simpa only [dist_eq_norm',div_mul_eq_mul_div] using hBound

theorem perturb_geometric_limit_zero {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {t K : ℝ} (ht : t < 1) (v : ℕ → V) (hZero : v 0=0)
    (hInc : ∀ k, ‖v (k+1)-v k‖ ≤ K*t^k) :
    ∃ vInf : V, Tendsto v atTop (𝓝 vInf) ∧ ‖vInf‖ ≤ K/(1-t) ∧
      ∀ k, ‖vInf-v k‖ ≤ (K/(1-t))*t^k := by
  obtain ⟨vInf,hLim,hTail⟩ := perturb_geometric_limit ht v hInc
  exact ⟨vInf,hLim,by simpa only [hZero,sub_zero,pow_zero,mul_one] using hTail 0,hTail⟩

theorem perturb_rpow_geometric_limit {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {rho sigma K : ℝ} (hr : 0 < rho) (hr1 : rho < 1) (hs : 0 < sigma)
    (v : ℕ → V) (hZero : v 0=0)
    (hInc : ∀ k : ℕ, ‖v (k+1)-v k‖ ≤ K*(rho^k : ℝ)^sigma) :
    ∃ vInf : V, Tendsto v atTop (𝓝 vInf) ∧ ‖vInf‖ ≤ K/(1-rho^sigma) ∧
      ∀ k : ℕ, ‖vInf-v k‖ ≤ (K/(1-rho^sigma))*(rho^k : ℝ)^sigma := by
  have ht : rho^sigma < 1 := Real.rpow_lt_one hr.le hr1 hs
  have hG : ∀ k : ℕ, ‖v (k+1)-v k‖ ≤ K*(rho^sigma)^k := by
    intro k
    rw [Real.rpow_pow_comm hr.le sigma k]
    exact hInc k
  obtain ⟨vInf,hLim,hNorm,hTail⟩ := perturb_geometric_limit_zero ht v hZero hG
  exact ⟨vInf,hLim,hNorm,fun k => by simpa only [Real.rpow_pow_comm hr.le sigma k] using hTail k⟩

end Yau.LeafProofs.L05Aux
