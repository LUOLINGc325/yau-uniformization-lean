import Yau.Proofs.C07Jets
import Yau.Proofs.C07Exponential
import Yau.LeafProofs.L17HolomorphicRegularity

open scoped ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Filter

variable {n : ℕ}

/-- The fixed-ball and inner-ball estimates imply the full frozen jet
estimate for every order, with constants independent of the later endpoint. -/
theorem transition_jet_bounds {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {s : ℝ → ℝ} {R C₀ σ B T₀ : ℝ} (hR : 0 < R) (hC₀ : 0 < C₀)
    (hclock : Tendsto s atTop atTop)
    (hhol : ∀ t u, T₀ ≤ t → t ≤ u → DifferentiableOn ℂ (F t u) (Metric.ball 0 R))
    (hfixed : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z ∈ Metric.ball (0 : ComplexVector n) R,
      ‖F t u z‖ ≤ B)
    (hinner : ∀ t u, T₀ ≤ t → t ≤ u → ∀ z ∈
      Metric.ball (0 : ComplexVector n) (Real.exp (-C₀ * s t)),
      ‖F t u z‖ ≤ Real.exp (-σ * s u)) :
    ∀ d : ℕ, ∃ Cd Td : ℝ, ∀ t u, Td ≤ t → t ≤ u →
      jetNorm (F t u) d ≤ Cd * min 1 (Real.exp (Cd * s t - σ * s u)) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1
    (hclock.eventually (Filter.eventually_ge_atTop (max 0 (-Real.log R / C₀))))
  intro d
  let A := ∑ k ∈ Finset.range (d + 1), cauchyFactor k
  let Bf := cauchyJetConstant d R * B
  let D := (d : ℝ) * C₀
  let C := max 1 (max A (max Bf D))
  have hC₁ : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC₁
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : Bf ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hDC : D ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, max T₀ T, ?_⟩
  intro t u ht htu
  have ht₀ : T₀ ≤ t := (le_max_left _ _).trans ht
  have hts := hT t ((le_max_right _ _).trans ht)
  have hs : 0 ≤ s t := (le_max_left _ _).trans hts
  have hlog : -Real.log R ≤ s t * C₀ :=
    (div_le_iff₀ hC₀).1 ((le_max_right _ _).trans hts)
  have hsmall : Real.exp (-C₀ * s t) ≤ R := by
    rw [← Real.exp_log hR]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcf : ContDiffOn ℂ ∞ (F t u) (Metric.ball 0 R) :=
    LeafProofs.L17Holomorphic.complexVector_contDiffOn Metric.isOpen_ball (hhol t u ht₀ htu)
  have hj₀ : jetNorm (F t u) d ≤ Bf := jetNorm_cauchy_bound hR hcf (hfixed t u ht₀ htu) d
  have hj₁ : jetNorm (F t u) d ≤ A * Real.exp (D * s t - σ * s u) :=
    jetNorm_inner_bound hC₀.le hs (hcf.mono (Metric.ball_subset_ball hsmall))
      (hinner t u ht₀ htu) d
  rw [mul_min_of_nonneg _ _ hC.le]
  refine le_min (by simpa only [mul_one] using hj₀.trans hBC) ?_
  calc
    jetNorm (F t u) d ≤ A * Real.exp (D * s t - σ * s u) := hj₁
    _ ≤ C * Real.exp (D * s t - σ * s u) :=
      mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le
    _ ≤ C * Real.exp (C * s t - σ * s u) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.exp_le_exp.mpr
        (sub_le_sub_right (mul_le_mul_of_nonneg_right hDC hs) _)

end Yau.Proofs.C07Aux
