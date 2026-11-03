import Yau.LeafProofs.L05PerturbationRescaledHolder

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_iter_base_data {n : ℕ} {ell L r eta c q : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (b : Space n →L[ℝ] ℝ) (A : Sym n)
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
    (hData : perturbBaseData ell L Phi f u) (hq : q=Phi A (0,0)+f (0,0))
    (hSup : ∀ p∈backward 1, |perturbIterSolution u c b A q r eta p| ≤ 1) :
    perturbBaseData ell L (perturbIterOperator Phi A r eta) (perturbIterSource f r eta)
      (perturbIterSolution u c b A q r eta) := by
  rcases hData with ⟨hC,hE,hConc,_,_,hu,_,hPDE⟩
  have hIter := perturb_iter_equation (eta := eta) (c := c) hr hr1 b A hu hPDE hq
  exact ⟨perturb_iter_operator_continuousOn hC hr hr1 A,
    fun p hp => perturb_iter_operator_elliptic hE hr hr1 A hp,
    fun p hp => perturb_iter_operator_concave hConc hr hr1 A hp,
    perturb_iter_operator_zero Phi A r eta,perturb_iter_source_zero f r eta,hIter.1,hSup,hIter.2⟩

theorem perturb_iter_holder_data {n : ℕ} {ell L r eta c q alpha beta mu af Astar : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (heta : 0 ≤ eta) (hmu : 0 ≤ mu)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (hA : ‖A‖ ≤ Astar)
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
    (hData : perturbHolderData ell L alpha beta mu af Phi f u)
    (hq : q=Phi A (0,0)+f (0,0))
    (hSup : ∀ p∈backward 1, |perturbIterSolution u c b A q r eta p| ≤ 1) :
    perturbHolderData ell L alpha beta (mu*(1+Astar)*r^(beta-eta)) (af*r^(alpha-eta))
      (perturbIterOperator Phi A r eta) (perturbIterSource f r eta)
      (perturbIterSolution u c b A q r eta) := by
  refine ⟨perturb_iter_base_data hr hr1 b A hData.1 hq hSup,?_,?_⟩
  · intro H p hp q' hq'
    exact perturb_iter_operator_holder_budget hr hr1 heta hmu hData.2.1 A H hA hp hq'
  · intro p hp q' hq'
    exact perturb_iter_source_holder hr hr1 hData.2.2 hp hq'

theorem perturb_back_weight_origin {n : ℕ} {sigma : ℝ} (hs : 0 < sigma)
    {p : Point n} (hp : p∈backward 1) : holderWeight sigma p (0,0) ≤ 2 := by
  have hpC : p∈perturbClosed (0 : Space n) 1 0 :=
    ⟨ball_subset_closedBall hp.1,by simpa only [one_pow,zero_sub] using hp.2.1.le,hp.2.2⟩
  exact perturb_closed_weight_origin hs hpC

theorem perturb_bounded_scaled_weight {c t W delta : ℝ} (hc : 0 ≤ c) (ht : t ≤ 1)
    (hW0 : 0 ≤ W) (hW2 : W ≤ 2) (hBudget : 4*c ≤ delta) : c*t*W ≤ delta := by
  have hct : c*t ≤ c := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hc
  have hh := mul_le_mul hct hW2 hW0 hc
  nlinarith only [hh,hBudget,hc]

theorem perturb_iter_small_data {n : ℕ} {ell L r eta c q alpha beta mu af Astar delta : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (heta : 0 ≤ eta) (ha : 0 < alpha) (hb : 0 < beta)
    (hea : eta ≤ alpha) (heb : eta ≤ beta) (hmu : 0 ≤ mu) (haf : 0 ≤ af)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (hA : ‖A‖ ≤ Astar)
    (hMuBudget : 4*(mu*(1+Astar)) ≤ delta) (hAfBudget : 4*af ≤ delta)
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
    (hData : perturbHolderData ell L alpha beta mu af Phi f u)
    (hq : q=Phi A (0,0)+f (0,0))
    (hSup : ∀ p∈backward 1, |perturbIterSolution u c b A q r eta p| ≤ 1) :
    perturbSmallData ell L delta (perturbIterOperator Phi A r eta) (perturbIterSource f r eta)
      (perturbIterSolution u c b A q r eta) := by
  have hZero : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hStar : 0 ≤ Astar := (norm_nonneg A).trans hA
  have hCoeff : 0 ≤ mu*(1+Astar) := mul_nonneg hmu (by linarith)
  refine ⟨perturb_iter_base_data hr hr1 b A hData.1 hq hSup,?_,?_⟩
  · intro H p hp
    have hRaw := perturb_iter_operator_holder_budget hr hr1 heta hmu hData.2.1 A H hA hp hZero
    have hW0 : 0 ≤ holderWeight beta p (0,0) :=
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    have hScalar := perturb_bounded_scaled_weight hCoeff (perturb_decay_power_le_one hr hr1 heb)
      hW0 (perturb_back_weight_origin hb hp) hMuBudget
    have hMul := mul_le_mul_of_nonneg_right hScalar (show 0 ≤ 1+‖H‖ by positivity)
    exact hRaw.trans (by nlinarith only [hMul])
  · intro p hp
    have hRaw := perturb_iter_source_holder (eta := eta) hr hr1 hData.2.2 hp hZero
    rw [perturb_iter_source_zero,sub_zero] at hRaw
    have hW0 : 0 ≤ holderWeight alpha p (0,0) :=
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    exact hRaw.trans (perturb_bounded_scaled_weight haf (perturb_decay_power_le_one hr hr1 hea)
      hW0 (perturb_back_weight_origin ha hp) hAfBudget)

end Yau.LeafProofs.L05Aux
