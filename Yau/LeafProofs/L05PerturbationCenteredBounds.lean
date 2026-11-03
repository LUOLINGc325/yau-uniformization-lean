import Yau.LeafProofs.L05PerturbationCenteredHolder
import Yau.LeafProofs.L05PerturbationRescaledData

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_center_zero_slope_bound {n : ℕ} {Phi : Sym n → Point n → ℝ} {f : Point n → ℝ}
    {alpha beta M fB : ℝ} (hb : 0 < beta) (hM : 0 ≤ M)
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
      |Phi H p-Phi H q| ≤ M*(1+‖H‖)*holderWeight beta p q)
    (hAnchor : |Phi 0 (0,0)| ≤ M) (hf : HolderBound alpha (backward 1) f fB)
    {z : Point n} (hz : z∈backward 1) : |Phi 0 z+f z| ≤ 3*M+fB := by
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hRaw := hCoeff 0 z hz (0,0) hOrigin
  simp only [norm_zero,add_zero,mul_one] at hRaw
  have hW := mul_le_mul_of_nonneg_left (perturb_back_weight_origin hb hz) hM
  have hPhi : |Phi 0 z| ≤ 3*M := by
    have hTri := abs_add_le (Phi 0 z-Phi 0 (0,0)) (Phi 0 (0,0))
    rw [sub_add_cancel] at hTri
    nlinarith only [hRaw,hW,hAnchor,hTri]
  have hF : |f z| ≤ fB := by simpa only [Real.norm_eq_abs] using hf.2.1 z hz
  exact (abs_add_le _ _).trans (by linarith only [hPhi,hF])

theorem perturb_normalize_sup_bound {n : ℕ} {u : Point n → ℝ} {uB Q0 : ℝ}
    (hSup : ∀ p∈backward 1, |u p| ≤ uB) (hQ0 : 0 ≤ Q0) (z : Point n)
    {r N q0 : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hN : 0 < N) (hBudget : 2*uB+Q0 ≤ N)
    (hq : |q0| ≤ Q0) (hBuf : perturbClosed z.1 r z.2⊆backward 1) :
    ∀ p∈backward 1, |perturbNormalize u z r N q0 p| ≤ 1 := by
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hzOrig : z∈backward 1 := by simpa only [perturbCenter_zero] using perturb_center_mem_original hr hBuf hOrigin
  have hR2 : r^2 ≤ 1 := by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr1),hr1]
  intro p hp
  have hZ := hSup _ (perturb_center_mem_original hr hBuf hp)
  have hz := hSup z hzOrig
  have ht : |p.2| ≤ 1 := by
    rw [abs_of_nonpos hp.2.2]
    have hLower := hp.2.1
    norm_num only [one_pow] at hLower
    linarith only [hLower]
  have hqt : |q0| * |p.2| ≤ Q0 := by
    simpa only [mul_one] using mul_le_mul hq ht (abs_nonneg _) hQ0
  have hPenalty : |r^2*q0*p.2| ≤ Q0 := by
    calc
      _ = r^2*(|q0| * |p.2|) := by rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg r)]; ring
      _ ≤ r^2*Q0 := mul_le_mul_of_nonneg_left hqt (sq_nonneg r)
      _ ≤ Q0 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hR2 hQ0
  have hFirst := abs_sub (u (perturbCenter z r p)) (u z)
  have hSecond := abs_sub (u (perturbCenter z r p)-u z) (r^2*q0*p.2)
  have hNumerator : |u (perturbCenter z r p)-u z-r^2*q0*p.2| ≤ 2*uB+Q0 := by
    linarith only [hZ,hz,hPenalty,hFirst,hSecond]
  rw [perturbNormalize,abs_div,abs_of_pos hN]
  exact (div_le_one hN).mpr (hNumerator.trans hBudget)

theorem perturb_normalization_ratio_le_one {r N : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hN1 : 1 ≤ N) :
    r^2/N ≤ 1 := by
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  apply (div_le_one hN).mpr
  have hR2 : r^2 ≤ 1 := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1),hr1]
  exact hR2.trans hN1

end Yau.LeafProofs.L05Aux
