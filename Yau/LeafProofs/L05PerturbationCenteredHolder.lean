import Yau.LeafProofs.L05PerturbationCenteredOperator
import Yau.LeafProofs.L05PerturbationWeights

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_centered_operator_holder {n : ℕ} {Phi : Sym n → Point n → ℝ} {beta M : ℝ}
    (hM : 0 ≤ M)
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
      |Phi H p-Phi H q| ≤ M*(1+‖H‖)*holderWeight beta p q)
    (z : Point n) {r N : ℝ} (hr : 0 < r) (hN : 0 < N) (hRatio : r^2/N ≤ 1)
    (hBuf : perturbClosed z.1 r z.2⊆backward 1) (H : Sym n)
    {p q : Point n} (hp : p∈backward 1) (hq : q∈backward 1) :
    |perturbCenteredOperator Phi z r N H p-perturbCenteredOperator Phi z r N H q| ≤ (M*r^beta)*(1+‖H‖)*holderWeight beta p q := by
  have hPref : 0 < r^2/N := div_pos (sq_pos_of_pos hr) hN
  have hScale : 0 < N/r^2 := div_pos hN (sq_pos_of_pos hr)
  have hRaw := hCoeff ((N/r^2) • H) _ (perturb_center_mem_original hr hBuf hp)
    _ (perturb_center_mem_original hr hBuf hq)
  rw [perturb_sym_smul_norm,abs_of_pos hScale,perturb_center_weight z hr] at hRaw
  have hDiff : perturbCenteredOperator Phi z r N H p-perturbCenteredOperator Phi z r N H q=
      (r^2/N)*(Phi ((N/r^2) • H) (perturbCenter z r p)-Phi ((N/r^2) • H) (perturbCenter z r q)) := by
    dsimp only [perturbCenteredOperator]
    ring
  rw [hDiff,abs_mul,abs_of_pos hPref]
  have hW : 0 ≤ holderWeight beta p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  calc
    _ ≤ (r^2/N)*(M*(1+(N/r^2)*‖H‖)*(r^beta*holderWeight beta p q)) :=
      mul_le_mul_of_nonneg_left hRaw hPref.le
    _ = (M*r^beta)*(r^2/N+‖H‖)*holderWeight beta p q := by
      field_simp [hr.ne',hN.ne']  <;>  ring
    _ ≤ _ := by
      have hFactor : r^2/N+‖H‖ ≤ 1+‖H‖ := by linarith only [hRatio]
      have hh := mul_le_mul_of_nonneg_left hFactor
        (mul_nonneg hM (Real.rpow_nonneg hr.le beta))
      exact mul_le_mul_of_nonneg_right hh hW

theorem perturb_centered_source_holder {n : ℕ} {f : Point n → ℝ} {alpha fB : ℝ}
    (hf : HolderBound alpha (backward 1) f fB) (z : Point n) {r N : ℝ}
    (hr : 0 < r) (hN : 0 < N) (hBuf : perturbClosed z.1 r z.2⊆backward 1)
    {p q : Point n} (hp : p∈backward 1) (hq : q∈backward 1) :
    |perturbCenteredSource f z r N p-perturbCenteredSource f z r N q| ≤ ((fB/N)*r^(2+alpha))*holderWeight alpha p q := by
  have hPref : 0 < r^2/N := div_pos (sq_pos_of_pos hr) hN
  have hRaw := hf.2.2 _ (perturb_center_mem_original hr hBuf hp) _ (perturb_center_mem_original hr hBuf hq)
  rw [Real.norm_eq_abs,perturb_center_weight z hr] at hRaw
  have hDiff : perturbCenteredSource f z r N p-perturbCenteredSource f z r N q=
      (r^2/N)*(f (perturbCenter z r p)-f (perturbCenter z r q)) := by
    dsimp only [perturbCenteredSource]
    ring
  rw [hDiff,abs_mul,abs_of_pos hPref]
  calc
    _ ≤ (r^2/N)*(fB*(r^alpha*holderWeight alpha p q)) := mul_le_mul_of_nonneg_left hRaw hPref.le
    _ = _ := by rw [Real.rpow_add hr,Real.rpow_two]; ring

end Yau.LeafProofs.L05Aux
