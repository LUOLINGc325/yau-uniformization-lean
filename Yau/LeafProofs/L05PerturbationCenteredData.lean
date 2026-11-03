import Yau.LeafProofs.L05PerturbationCenteredBounds

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_centered_holder_data {n : ℕ} {ell L alpha beta M fB uB mu0 af0 : ℝ}
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ} (hb : 0 < beta) (hM : 0 ≤ M)
    (hJoint : ContinuousOn (fun a : Sym n × Point n => Phi a.1 a.2) (univ ×ˢ backward 1))
    (hE : ∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L)
    (hConc : ∀ p∈backward 1, ConcaveOn ℝ univ (fun H => Phi H p))
    (hCoeff : ∀ H : Sym n, ∀ p∈backward 1, ∀ q∈backward 1,
      |Phi H p-Phi H q| ≤ M*(1+‖H‖)*holderWeight beta p q)
    (hAnchor : |Phi 0 (0,0)| ≤ M) (hf : HolderBound alpha (backward 1) f fB)
    (hu : C2 (backward 1) u) (hSup : ∀ p∈backward 1, |u p| ≤ uB)
    (hPDE : ∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p)
    (z : Point n) {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hN1 : 1 ≤ N)
    (hBudget : 2*uB+(3*M+fB) ≤ N) (hBuf : perturbClosed z.1 r z.2⊆backward 1)
    (hMu : M*r^beta ≤ mu0) (hAf : (fB/N)*r^(2+alpha) ≤ af0) :
    perturbHolderData ell L alpha beta mu0 af0
      (perturbCenteredOperator Phi z r N) (perturbCenteredSource f z r N)
      (perturbNormalize u z r N (Phi 0 z+f z)) := by
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hRatio := perturb_normalization_ratio_le_one hr.le hr1 hN1
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hzOrig : z∈backward 1 := by simpa only [perturbCenter_zero] using perturb_center_mem_original hr hBuf hOrigin
  have hSlope := perturb_center_zero_slope_bound hb hM hCoeff hAnchor hf hzOrig
  have hQ0 : 0 ≤ 3*M+fB := by have hf0 := hf.1; positivity
  have hEq := perturb_centered_equation (N := N) (q0 := Phi 0 z+f z) hu hPDE z hr hN hBuf rfl
  refine ⟨⟨perturb_centered_operator_continuousOn hJoint z hr hBuf,
    fun p hp => perturb_centered_operator_elliptic hE z hr hN hBuf hp,
    fun p hp => perturb_centered_operator_concave hConc z hr hN hBuf hp,
    perturb_centered_operator_zero Phi z r N,perturb_centered_source_zero f z r N,hEq.1,
    perturb_normalize_sup_bound hSup hQ0 z hr hr1 hN hBudget hSlope hBuf,hEq.2⟩,?_,?_⟩
  · intro H p hp q hq
    have hRaw := perturb_centered_operator_holder hM hCoeff z hr hN hRatio hBuf H hp hq
    have hW0 : 0 ≤ holderWeight beta p q :=
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    have hBudget' := mul_le_mul_of_nonneg_right hMu
      (mul_nonneg (show 0 ≤ 1+‖H‖ by positivity) hW0)
    exact hRaw.trans (by nlinarith only [hBudget'])
  · intro p hp q hq
    have hRaw := perturb_centered_source_holder hf z hr hN hBuf hp hq
    have hW0 : 0 ≤ holderWeight alpha p q :=
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    exact hRaw.trans (mul_le_mul_of_nonneg_right hAf hW0)

end Yau.LeafProofs.L05Aux
