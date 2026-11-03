import Yau.Proofs.C02LinearPrecompositionJets
import Mathlib.Analysis.Calculus.MeanValue

/-! A single dilation is chosen from a fixed finite jet majorant before
every field. Its value vanishes at the origin; the zeroth jet is controlled
by the same first-derivative majorant used for all members of the family. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_uniform_finiteJet_dilation (ρ : ℝ) (hρ : 0 < ρ)
    (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 2 * r < ρ ∧
      ∀ f : E → F, ContDiffOn ℝ ∞ f (Metric.ball 0 ρ) → f 0 = 0 →
      (∀ k ≤ q + 1, ∀ y ∈ Metric.ball (0 : E) ρ, ‖iteratedFDeriv ℝ k f y‖ ≤ K k) →
      ∀ k ≤ q, ∀ z ∈ Metric.closedBall (0 : E) 2,
        ‖iteratedFDeriv ℝ k (fun y => f (r • y)) z‖ ≤ ε := by
  let B := 1 + ∑ j : Fin (q + 2), K j
  have hsum : 0 ≤ ∑ j : Fin (q + 2), K j := Finset.sum_nonneg (fun j _ => hK j)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hKB (k : ℕ) (hk : k < q + 2) : K k ≤ B := by
    have hh : K (⟨k, hk⟩ : Fin (q + 2)) ≤ ∑ j : Fin (q + 2), K j :=
      Finset.single_le_sum (f := fun j : Fin (q + 2) => K j)
        (fun j _ => hK j) (Finset.mem_univ (⟨k, hk⟩ : Fin (q + 2)))
    dsimp only [B]
    linarith
  let r := min (ρ / 4) (min 1 (ε / (4 * B)))
  have hr : 0 < r := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hrρ : r ≤ ρ / 4 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε / (4 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hBr : 4 * B * r ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 4 * B by positivity)).mp hrε
    nlinarith
  have h2r : 2 * r < ρ := by linarith
  refine ⟨r, hr, hr1, h2r, ?_⟩
  intro f hf hf0 hbound k hk z hz
  have hzn : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hy : r • z ∈ Metric.ball (0 : E) ρ := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hzn hr.le).trans_lt (by nlinarith)
  by_cases hk0 : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    have hdiff (y : E) (hy : y ∈ Metric.ball (0 : E) ρ) : DifferentiableAt ℝ f y :=
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
    have hderiv (y : E) (hy : y ∈ Metric.ball (0 : E) ρ) : ‖fderiv ℝ f y‖ ≤ B := by
      rw [← norm_iteratedFDeriv_one]
      exact (hbound 1 (by omega) y hy).trans (hKB 1 (by omega))
    have hh := (convex_ball (0 : E) ρ).norm_image_sub_le_of_norm_fderiv_le hdiff hderiv
      (Metric.mem_ball_self hρ) hy
    rw [hf0, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hzn hr.le) hB.le).trans (by nlinarith))
  · have hpow : r ^ k ≤ r := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      rw [pow_succ]
      exact mul_le_of_le_one_left hr.le (pow_le_one₀ hr.le hr1)
    calc
      _ ≤ ‖iteratedFDeriv ℝ k f (r • z)‖ * |r| ^ k :=
        norm_iteratedFDeriv_comp_smulOn_le Metric.isOpen_ball hf r z hy k
      _ ≤ B * r ^ k := by
        rw [abs_of_pos hr]
        exact mul_le_mul_of_nonneg_right
          ((hbound k (by omega) _ hy).trans (hKB k (by omega))) (pow_nonneg hr.le k)
      _ ≤ B * r := mul_le_mul_of_nonneg_left hpow hB.le
      _ ≤ ε := by nlinarith

end Yau.Blueprint.C02Proof
