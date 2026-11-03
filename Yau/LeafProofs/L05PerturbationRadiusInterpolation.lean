import Yau.LeafProofs.L05PerturbationSeries
import Yau.LeafProofs.L05PerturbationOscillation

open Filter Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_power_radius_index {rho r : ℝ} (hRho : 0 < rho) (hRho1 : rho < 1)
    (hr : 0 < r) (hrRho : r ≤ rho) :
    ∃ k : ℕ, 1 ≤ k ∧ rho^(k+1) < r ∧ r ≤ rho^k := by
  obtain ⟨k,hLo,hHi⟩ := exists_nat_pow_near_of_lt_one hr (hrRho.trans hRho1.le) hRho hRho1
  refine ⟨k,?_,hLo,hHi⟩
  by_contra h
  have hk : k=0 := by omega
  have hh : rho < r := by simpa only [hk,zero_add,pow_one] using hLo
  exact (not_lt_of_ge hrRho) hh

theorem perturb_discrete_radius_bound {n : ℕ} {rho sigma J : ℝ}
    (hRho : 0 < rho) (hRho1 : rho < 1) (hs : 0 ≤ sigma) (hJ : 0 ≤ J)
    (u P : Point n → ℝ)
    (hBound : ∀ k : ℕ, 1 ≤ k → ∀ p∈perturbClosed (0 : Space n) (rho^k) 0,
      |u p-P p| ≤ J*(rho^k : ℝ)^sigma) :
    ∀ r : ℝ, 0 < r → r ≤ rho → ∀ p∈perturbClosed (0 : Space n) r 0,
      |u p-P p| ≤ (J*rho^(-sigma))*r^sigma := by
  intro r hr hrRho p hp
  obtain ⟨k,hk,hLo,hHi⟩ := perturb_power_radius_index hRho hRho1 hr hrRho
  have hMem := perturb_closed_subset_radius (0 : Space n) hr.le hHi 0 hp
  have hScale : rho^k ≤ r/rho := by
    apply (le_div_iff₀ hRho).mpr
    simpa only [pow_succ] using hLo.le
  have hPower : (rho^k : ℝ)^sigma ≤ rho^(-sigma)*r^sigma := by
    calc
      _ ≤ (r/rho)^sigma := Real.rpow_le_rpow (pow_nonneg hRho.le k) hScale hs
      _ = _ := by rw [Real.div_rpow hr.le hRho.le,Real.rpow_neg hRho.le]; ring
  exact (hBound k hk p hMem).trans (by nlinarith only [mul_le_mul_of_nonneg_left hPower hJ])

end Yau.LeafProofs.L05Aux
