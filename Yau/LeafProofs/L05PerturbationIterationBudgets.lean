import Yau.LeafProofs.L05PerturbationRescaledData
import Yau.LeafProofs.L05PerturbationPolynomialUpdate

open Filter Set Metric
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_geometric_partial_identity (t : ℝ) (k : ℕ) :
    (∑ i∈Finset.range k, t^i)*(1-t)=1-t^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,pow_succ]
    linear_combination ih

theorem perturb_geometric_partial_budget {t K : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hK : 0 ≤ K) (k : ℕ) : K*(∑ i∈Finset.range k, t^i) ≤ K/(1-t) := by
  apply (le_div_iff₀ (sub_pos.mpr ht1)).mpr
  rw [mul_assoc,perturb_geometric_partial_identity]
  nlinarith only [mul_nonneg hK (pow_nonneg ht k)]

theorem perturb_increment_partial_budget {V : Type*} [NormedAddCommGroup V] {t K : ℝ}
    (v : ℕ → V) (hZero : v 0=0)
    (hInc : ∀ k, ‖v (k+1)-v k‖ ≤ K*t^k) (k : ℕ) :
    ‖v k‖ ≤ K*(∑ i∈Finset.range k, t^i) := by
  have hDist := dist_le_range_sum_of_dist_le k (f := v) (d := fun i => K*t^i)
    (fun {i} _ => by simpa only [dist_eq_norm'] using hInc i)
  simpa only [hZero,dist_zero_left,← Finset.mul_sum] using hDist

theorem perturb_matrix_partial_update {n : ℕ} {t K a : ℝ} {k : ℕ} (ht : 0 ≤ t)
    (A B : Sym n) (hA : ‖A‖ ≤ K*(∑ i∈Finset.range k, t^i)) (hB : ‖B‖ ≤ K) (ha : a=t^k) :
    ‖A+a • B‖ ≤ K*(∑ i∈Finset.range (k+1), t^i) := by
  have hScalar : ‖a • B‖ ≤ K*t^k := by
    rw [perturb_sym_smul_norm,ha,abs_of_nonneg (pow_nonneg ht k)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hB (pow_nonneg ht k)
  have hTri := norm_add_le A (a • B)
  rw [Finset.sum_range_succ,mul_add]
  linarith only [hA,hScalar,hTri]

theorem perturb_iteration_smallness_budgets {rho eta K delta : ℝ} (hr : 0 < rho)
    (hr1 : rho < 1) (he : 0 < eta) (hK : 0 < K) (hd : 0 < delta) :
    let Astar := K/(1-rho^eta)
    let mu := delta/(4*(1+Astar))
    let af := delta/4
    0 < Astar ∧ 0 < mu ∧ 0 < af ∧ 4*(mu*(1+Astar))=delta ∧ 4*af=delta := by
  let Astar := K/(1-rho^eta)
  have hA : 0 < Astar := div_pos hK (sub_pos.mpr (Real.rpow_lt_one hr.le hr1 he))
  have hDen : 0 < 4*(1+Astar) := by positivity
  refine ⟨hA,div_pos hd hDen,by positivity,?_,by ring⟩
  change 4*((delta/(4*(1+Astar)))*(1+Astar))=delta
  calc
    _ = (delta/(4*(1+Astar)))*(4*(1+Astar)) := by ring
    _ = delta := div_mul_cancel₀ delta hDen.ne'

end Yau.LeafProofs.L05Aux
