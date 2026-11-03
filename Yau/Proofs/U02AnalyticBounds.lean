import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.ContDiff.Basic

open scoped ContDiff Topology
open Set Metric

namespace U02AnalyticAux

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem differentiableOn_iteratedFDeriv_of_complex_infty
    {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℂ ∞ f s) (j : ℕ) :
    DifferentiableOn ℂ (iteratedFDeriv ℂ j f) s := by
  intro y hy
  exact ((hf.contDiffAt (hs.mem_nhds hy)).differentiableAt_iteratedFDeriv
    (m := j) (by exact_mod_cast ENat.natCast_lt_top j)).differentiableWithinAt

theorem norm_fderiv_le_two_mul_div_of_bound
    {f : E → F} {x : E} {r C : ℝ}
    (hr : 0 < r) (_hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f (ball x r))
    (hb : ∀ y ∈ ball x r, ‖f y‖ ≤ C) :
    ‖fderiv ℂ f x‖ ≤ 2 * C / r := by
  have hcx : ‖f x‖ ≤ C := hb x (mem_ball_self hr)
  have hm : MapsTo f (ball x r) (closedBall (f x) (2 * C)) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb y hy])
  exact Complex.norm_fderiv_le_div_of_mapsTo_ball hf hm hr

theorem norm_iteratedFDeriv_le_shrinking_balls
    {f : E → F} {x : E} {R C δ : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hf : ContDiffOn ℂ ∞ f (ball x R))
    (hb : ∀ y ∈ ball x R, ‖f y‖ ≤ C) :
    ∀ j : ℕ, ∀ y ∈ ball x (R - (j : ℝ) * δ),
      ‖iteratedFDeriv ℂ j f y‖ ≤ C * (2 / δ)^j := by
  intro j
  induction j with
  | zero =>
    intro y hy
    simpa using hb y (by simpa using hy)
  | succ j ih =>
    intro y hy
    have hsmall : ball y δ ⊆ ball x (R - (j : ℝ) * δ) := by
      intro z hz
      rw [mem_ball] at hz hy ⊢
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ < δ + (R - ((j + 1 : ℕ) : ℝ) * δ) := add_lt_add hz hy
        _ = R - (j : ℝ) * δ := by push_cast; ring
    have hlarge : ball x (R - (j : ℝ) * δ) ⊆ ball x R := by
      apply ball_subset_ball
      have : 0 ≤ (j : ℝ) * δ := mul_nonneg (Nat.cast_nonneg j) hδ.le
      linarith
    have hdiff := (differentiableOn_iteratedFDeriv_of_complex_infty isOpen_ball hf j).mono
      (hsmall.trans hlarge)
    have hbound := norm_fderiv_le_two_mul_div_of_bound hδ
      (mul_nonneg hC (pow_nonneg (by positivity) _)) hdiff (fun z hz => ih z (hsmall hz))
    rw [norm_fderiv_iteratedFDeriv] at hbound
    calc
      ‖iteratedFDeriv ℂ (j + 1) f y‖ ≤ 2 * (C * (2 / δ)^j) / δ := hbound
      _ = C * (2 / δ)^(j + 1) := by rw [pow_succ]; ring

theorem norm_iteratedFDeriv_center_le
    {f : E → F} {x : E} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ContDiffOn ℂ ∞ f (ball x R))
    (hb : ∀ y ∈ ball x R, ‖f y‖ ≤ C) (k : ℕ) :
    ‖iteratedFDeriv ℂ k f x‖ ≤ C * (2 * ((k : ℝ) + 1) / R)^k := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hδ : 0 < R / ((k : ℝ) + 1) := div_pos hR hk
  have hr : R - (k : ℝ) * (R / ((k : ℝ) + 1)) = R / ((k : ℝ) + 1) := by
    field_simp
    ring
  have heq : 2 / (R / ((k : ℝ) + 1)) = 2 * ((k : ℝ) + 1) / R := by field_simp
  have h := norm_iteratedFDeriv_le_shrinking_balls hR hC hδ hf hb k x
    (by rw [hr]; exact mem_ball_self hδ)
  simpa only [heq] using h

end U02AnalyticAux
