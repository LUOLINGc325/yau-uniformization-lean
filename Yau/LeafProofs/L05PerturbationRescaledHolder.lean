import Yau.LeafProofs.L05PerturbationRescaledOperator
import Yau.LeafProofs.L05PerturbationWeights

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_iter_operator_holder_raw {n : ℕ} {r eta beta mu : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {Phi : Sym n → Point n → ℝ}
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
      |Phi H p-Phi H q| ≤ mu*(1+‖H‖)*holderWeight beta p q)
    (A H : Sym n) {p q : Point n} (hp : p∈backward 1) (hq : q∈backward 1) :
    |perturbIterOperator Phi A r eta H p-perturbIterOperator Phi A r eta H q| ≤
      mu*r^(beta-eta)*(1+‖A+r^eta • H‖)*holderWeight beta p q := by
  have hInv : 0 < (r^eta)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hr eta)
  have hRaw := hCoeff (A+r^eta • H) _ (perturb_scale_back_mem hr hr1 hp)
    _ (perturb_scale_back_mem hr hr1 hq)
  have hDiff : perturbIterOperator Phi A r eta H p-perturbIterOperator Phi A r eta H q=
      (r^eta)⁻¹*(Phi (A+r^eta • H) (perturbScale r p)-Phi (A+r^eta • H) (perturbScale r q)) := by
    dsimp only [perturbIterOperator]
    ring
  rw [hDiff,abs_mul,abs_of_pos hInv]
  calc
    _ ≤ (r^eta)⁻¹*(mu*(1+‖A+r^eta • H‖)*holderWeight beta (perturbScale r p) (perturbScale r q)) :=
      mul_le_mul_of_nonneg_left hRaw hInv.le
    _ = _ := by rw [perturb_scale_weight hr,Real.rpow_sub hr]; ring

theorem perturb_iter_source_holder {n : ℕ} {r eta alpha af : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {f : Point n → ℝ}
    (hf : ∀ p∈backward 1, ∀ q∈backward 1, |f p-f q| ≤ af*holderWeight alpha p q)
    {p q : Point n} (hp : p∈backward 1) (hq : q∈backward 1) :
    |perturbIterSource f r eta p-perturbIterSource f r eta q| ≤
      af*r^(alpha-eta)*holderWeight alpha p q := by
  have hInv : 0 < (r^eta)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hr eta)
  have hRaw := hf _ (perturb_scale_back_mem hr hr1 hp) _ (perturb_scale_back_mem hr hr1 hq)
  have hDiff : perturbIterSource f r eta p-perturbIterSource f r eta q=
      (r^eta)⁻¹*(f (perturbScale r p)-f (perturbScale r q)) := by
    dsimp only [perturbIterSource]
    ring
  rw [hDiff,abs_mul,abs_of_pos hInv]
  calc
    _ ≤ (r^eta)⁻¹*(af*holderWeight alpha (perturbScale r p) (perturbScale r q)) :=
      mul_le_mul_of_nonneg_left hRaw hInv.le
    _ = _ := by rw [perturb_scale_weight hr,Real.rpow_sub hr]; ring

theorem perturb_iter_operator_holder {n : ℕ} {r eta beta mu : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hmu : 0 ≤ mu) {Phi : Sym n → Point n → ℝ}
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
      |Phi H p-Phi H q| ≤ mu*(1+‖H‖)*holderWeight beta p q)
    (A H : Sym n) {p q : Point n} (hp : p∈backward 1) (hq : q∈backward 1) :
    |perturbIterOperator Phi A r eta H p-perturbIterOperator Phi A r eta H q| ≤
      mu*r^(beta-eta)*(1+‖A‖+r^eta*‖H‖)*holderWeight beta p q := by
  have hRaw := perturb_iter_operator_holder_raw (eta := eta) hr hr1 hCoeff A H hp hq
  have hNorm := norm_add_le A (r^eta • H)
  rw [perturb_sym_smul_norm,abs_of_pos (Real.rpow_pos_of_pos hr eta)] at hNorm
  have hN : 1+‖A+r^eta • H‖ ≤ 1+‖A‖+r^eta*‖H‖ := by linarith only [hNorm]
  have hW : 0 ≤ holderWeight beta p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hFactor : 0 ≤ mu*r^(beta-eta)*holderWeight beta p q :=
    mul_nonneg (mul_nonneg hmu (Real.rpow_nonneg hr.le _)) hW
  have hMul := mul_le_mul_of_nonneg_left hN hFactor
  exact hRaw.trans (by nlinarith only [hMul])

theorem perturb_iter_operator_holder_budget {n : ℕ} {r eta beta mu Astar : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (heta : 0 ≤ eta) (hmu : 0 ≤ mu)
    {Phi : Sym n → Point n → ℝ}
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
      |Phi H p-Phi H q| ≤ mu*(1+‖H‖)*holderWeight beta p q)
    (A H : Sym n) (hA : ‖A‖ ≤ Astar) {p q : Point n} (hp : p∈backward 1) (hq : q∈backward 1) :
    |perturbIterOperator Phi A r eta H p-perturbIterOperator Phi A r eta H q| ≤
      mu*(1+Astar)*r^(beta-eta)*(1+‖H‖)*holderWeight beta p q := by
  have hRaw := perturb_iter_operator_holder (eta := eta) hr hr1 hmu hCoeff A H hp hq
  have hStar : 0 ≤ Astar := (norm_nonneg A).trans hA
  have hRE := Real.rpow_le_one hr.le hr1 heta
  have hREH := mul_le_mul_of_nonneg_right hRE (norm_nonneg H)
  have hStarH := mul_nonneg hStar (norm_nonneg H)
  have hN : 1+‖A‖+r^eta*‖H‖ ≤ (1+Astar)*(1+‖H‖) := by nlinarith only [hA,hREH,hStarH]
  have hW : 0 ≤ holderWeight beta p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hFactor : 0 ≤ mu*r^(beta-eta)*holderWeight beta p q :=
    mul_nonneg (mul_nonneg hmu (Real.rpow_nonneg hr.le _)) hW
  have hMul := mul_le_mul_of_nonneg_left hN hFactor
  exact hRaw.trans (by nlinarith only [hMul])

theorem perturb_decay_power_le_one {r eta beta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (he : eta ≤ beta) : r^(beta-eta) ≤ 1 :=
  Real.rpow_le_one hr.le hr1 (sub_nonneg.mpr he)

end Yau.LeafProofs.L05Aux
