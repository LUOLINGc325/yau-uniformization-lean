import Yau.Proofs.C04BoundedGeometryChartsCayleyModelJets

/-! One source radius and uniform Cayley jets precede the entire coframe family. -/
noncomputable section
open Set
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem exists_uniform_coframe_cayley_jet_bounds (n : ℕ) (R : ℝ) (hR : 0 < R)
    (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ s : ℝ, 0 < s ∧ s ≤ R ∧ ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ A : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
        ContDiff ℝ ∞ A → A 0 = ContinuousLinearMap.id ℝ (ComplexVector n) →
        (∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R → ‖iteratedFDeriv ℝ m A x‖ ≤ B m) →
        (∀ x ∈ Metric.closedBall (0 : ComplexVector n) s,
          (A x).IsInvertible ∧ (coframeComplexModel n (A x) + stdComplex n).IsInvertible) ∧
        ContDiffOn ℝ ∞ (fun y => coframeCayleyGraphModel n (A y)) (Metric.ball (0 : ComplexVector n) s) ∧
        ∀ m x, x ∈ Metric.ball (0 : ComplexVector n) s →
          ‖iteratedFDeriv ℝ m (fun y => coframeCayleyGraphModel n (A y)) x‖ ≤ C m := by
  obtain ⟨d, hd, D, hD, hmodel⟩ := exists_coframe_cayley_model_jet_bounds n
  have hB1 := hB 1
  let s := min (R / 2) (d / (4 * (1 + B 1)))
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsR : s ≤ R := (min_le_left _ _).trans (by linarith)
  have hsprod : s * (4 * (1 + B 1)) ≤ d :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let C := fun m => 1 + (m.factorial : ℝ) *
    (1 + ∑ j ∈ Finset.range (m + 1), D j) * (1 + ∑ j ∈ Finset.range (m + 1), B j)^m
  have hC (m : ℕ) : 0 < C m := by
    have hb := Finset.sum_nonneg (f := B) (fun j _ => (hB j).le) (s := Finset.range (m + 1))
    have hd := Finset.sum_nonneg (f := D) (fun j _ => (hD j).le) (s := Finset.range (m + 1))
    dsimp [C]
    positivity
  refine ⟨s, hs, hsR, C, hC, ?_⟩
  intro A hA hA0 hjet
  have hnear (x : ComplexVector n) (hx : x ∈ Metric.closedBall (0 : ComplexVector n) s) :
      ‖A x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ < d := by
    have hxn : ‖x‖ ≤ s := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hxR : x ∈ Metric.closedBall (0 : ComplexVector n) R := Metric.closedBall_subset_closedBall hsR hx
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => hA.differentiable (by simp) y)
      (fun y hy => by simpa only [norm_iteratedFDeriv_one] using hjet 1 y hy)
      (convex_closedBall (0 : ComplexVector n) R) (Metric.mem_closedBall_self hR.le) hxR
    rw [hA0, sub_zero] at hh
    have hp := mul_le_mul_of_nonneg_left hxn (hB 1).le
    nlinarith [mul_nonneg hs.le (hB 1).le]
  let T := Metric.ball (ContinuousLinearMap.id ℝ (ComplexVector n)) d
  have hg : ContDiffOn ℝ ∞ (coframeCayleyGraphModel n) T := by
    intro L hL
    have hn : ‖L - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ d :=
      (show ‖L - ContinuousLinearMap.id ℝ (ComplexVector n)‖ < d by
        simpa only [T, Metric.mem_ball, dist_eq_norm] using hL).le
    exact (coframeCayleyGraphModel_smoothAt L (hmodel L hn).1 (hmodel L hn).2.1).contDiffWithinAt
  have hmap : MapsTo A (Metric.ball (0 : ComplexVector n) s) T := by
    intro x hx
    simpa only [T, Metric.mem_ball, dist_eq_norm] using hnear x (Metric.ball_subset_closedBall hx)
  refine ⟨(fun x hx => ⟨(hmodel (A x) (hnear x hx).le).1,
      (hmodel (A x) (hnear x hx).le).2.1⟩), hg.comp hA.contDiffOn hmap, ?_⟩
  intro m x hx
  let Db := 1 + ∑ j ∈ Finset.range (m + 1), D j
  let Lb := 1 + ∑ j ∈ Finset.range (m + 1), B j
  have hDb (j : ℕ) (hj : j ≤ m) : D j ≤ Db := by
    have hh := Finset.single_le_sum (f := D) (fun k _ => (hD k).le)
      (show j ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
    dsimp [Db]
    linarith
  have hLb : 1 ≤ Lb := by
    have hh := Finset.sum_nonneg (f := B) (fun j _ => (hB j).le) (s := Finset.range (m + 1))
    dsimp [Lb]
    linarith
  have hBj (j : ℕ) (hj : j ≤ m) : B j ≤ Lb := by
    have hh := Finset.single_le_sum (f := B) (fun k _ => (hB k).le)
      (show j ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
    dsimp [Lb]
    linarith
  have hcc : ∀ j ≤ m, ‖iteratedFDerivWithin ℝ j (coframeCayleyGraphModel n) T (A x)‖ ≤ Db := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball (hmap hx)]
    exact ((hmodel (A x) (hnear x (Metric.ball_subset_closedBall hx)).le).2.2 j).trans (hDb j hj)
  have hbb : ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDerivWithin ℝ j A (Metric.ball (0 : ComplexVector n) s) x‖ ≤ Lb^j := by
    intro j hj hjm
    rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hx]
    exact (hjet j x (Metric.closedBall_subset_closedBall hsR (Metric.ball_subset_closedBall hx))).trans
      ((hBj j hjm).trans (by simpa only [pow_one] using pow_le_pow_right₀ hLb hj))
  have HH := norm_iteratedFDerivWithin_comp_le hg hA.contDiffOn (by simp : (m : ℕ∞ω) ≤ ∞)
    Metric.isOpen_ball.uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn hmap hx hcc hbb
  rw [iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hx] at HH
  exact HH.trans (by dsimp [C, Db, Lb]; linarith)

end Yau.Proofs.C04ChartsAux
