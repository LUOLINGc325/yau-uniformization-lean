import Mathlib

/-!
Scalar estimates used in `charts.tex:1031–1070`.  The later endpoint remains
arbitrary: the interpolation error is absorbed using only `s ≤ u`.
-/

namespace Yau.Proofs.C07Aux

open Filter

/-- The inner-ball and fixed-ball Cauchy bounds have the exact minimum form
used for every jet order in the shrinking-chart proposition. -/
theorem combine_jet_bounds {J A B D s σ u : ℝ}
    (hJ₀ : J ≤ B) (hJ₁ : J ≤ A * Real.exp (D * s - σ * u))
    (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ J ≤ C * min 1 (Real.exp (C * s - σ * u)) := by
  let C := max 1 (max A (max B D))
  have hC₁ : 1 ≤ C := le_max_left _ _
  have hAC : A ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hBC : B ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)
  have hDC : D ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC₁
  refine ⟨C, hC, ?_⟩
  rw [mul_min_of_nonneg _ _ hC.le]
  refine le_min (by simpa using hJ₀.trans hBC) ?_
  calc
    J ≤ A * Real.exp (D * s - σ * u) := hJ₁
    _ ≤ C * Real.exp (D * s - σ * u) :=
      mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le
    _ ≤ C * Real.exp (C * s - σ * u) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_right hDC hs) _)) hC.le

/-- A quantitative lower bound for the three-circle interpolation weight. -/
theorem interpolation_weight_lower {C₀ γ L s : ℝ}
    (hC : 0 < C₀) (hγ : 0 < γ) (hγC : γ ≤ C₀)
    (hL : L ≤ 0) (hs : 0 < s) (hlarge : -2 * L ≤ γ * s) :
    γ / (2 * C₀) ≤ (L + γ * s) / (L + C₀ * s) := by
  have hγs : 0 < γ * s := mul_pos hγ hs
  have hγCs : γ * s ≤ C₀ * s := mul_le_mul_of_nonneg_right hγC hs.le
  have hden : 0 < L + C₀ * s := by nlinarith
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * C₀) hden).2
  nlinarith [mul_nonneg (neg_nonneg.mpr hL) hC.le]

/-- The bounded outer-circle term is absorbed with one threshold that works
for every later endpoint. -/
theorem absorb_interpolation_error {C₀ γ σ θ B s u : ℝ}
    (hC : 0 < C₀) (hγ : 0 < γ) (hσ : 0 < σ)
    (hθ₀ : 0 ≤ θ)
    (hθ : γ / (2 * C₀) ≤ θ) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (hsu : s ≤ u)
    (hlarge : B ≤ σ * γ * s / (4 * C₀)) :
    -θ * σ * u + (1 - θ) * B ≤ -(σ / (4 * C₀)) * γ * u := by
  have hu : 0 ≤ u := hs.trans hsu
  have hθ' : γ ≤ θ * (2 * C₀) := (div_le_iff₀ (by positivity)).1 hθ
  have hlarge' : B * (4 * C₀) ≤ σ * γ * s :=
    (le_div_iff₀ (by positivity)).1 hlarge
  have hBs : B * (4 * C₀) ≤ σ * γ * u :=
    hlarge'.trans (mul_le_mul_of_nonneg_left hsu (mul_pos hσ hγ).le)
  have hmain := mul_le_mul_of_nonneg_right hθ' (mul_nonneg hσ.le hu)
  have herr : (1 - θ) * B ≤ B := by nlinarith
  calc
    -θ * σ * u + (1 - θ) * B ≤ (-σ * γ * u) / (4 * C₀) :=
      (le_div_iff₀ (by positivity)).2 (by nlinarith)
    _ = -(σ / (4 * C₀)) * γ * u := by ring

end Yau.Proofs.C07Aux
