import Yau.LeafProofs.L14TwoMultipliers

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

/-- The actual distance cutoffs exhaust every compact set uniformly, while
retaining the quantitative gradient and support bounds. -/
theorem exists_weightedDbar_cutoff_exhaustion_compact {d : ℕ} (N : ComplexManifold d)
    (g : Yau.SmoothMetric N) (o : N.Carrier) :
    ∃ C : ℝ, 0 < C ∧ ∃ η : ℕ → N.Carrier → ℝ,
      (∀ m, SmoothFn (η m) ∧ HasCompactSupport (η m) ∧
        (∀ y, η m y ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ y, inducedDistance g.form o y ≤ (m : ℝ) + 1 → η m y = 1) ∧
        tsupport (η m) ⊆ {y | inducedDistance g.form o y ≤ 2 * ((m : ℝ) + 1)} ∧
        ∀ y, gradNormSq g.form (η m) y ≤ (C / ((m : ℝ) + 1)) ^ 2 / 2) ∧
      (∀ x, ∀ᶠ m in atTop, η m x = 1) ∧
      ∀ K : Set N.Carrier, IsCompact K → ∀ᶠ m in atTop, ∀ x ∈ K, η m x = 1 := by
  obtain ⟨C, hC, η, hη, hpoint⟩ := exists_weightedDbar_cutoff_exhaustion N g o
  refine ⟨C, hC, η, hη, hpoint, ?_⟩
  intro K hK
  have hd : Continuous (fun x => inducedDistance g.form o x) := L12Aux.continuous_distFrom g o
  obtain ⟨B, hB⟩ := hK.bddAbove_image hd.continuousOn
  obtain ⟨k, hk⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop k] with m hm
  intro x hx
  apply (hη m).2.2.2.1 x
  have hBx : inducedDistance g.form o x ≤ B := hB ⟨x, hx, rfl⟩
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast hm
  linarith

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

/-- Gradient contractions on the actual weighted Hilbert completion tend to
zero whenever their nonnegative squared-gradient bounds tend to zero. -/
theorem weightedTwoHilbertGradientContraction_tendsto_zero
    (χ : ℕ → M.Carrier → ℝ) (hχ : ∀ m, SmoothFn (χ m))
    (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hgrad : ∀ m x, gradNormSq g.form (χ m) x ≤ A m)
    (hAtop : Tendsto A atTop (𝓝 0))
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) :
    Tendsto (fun m => weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ
      (χ m) (hχ m) (A m) (hA m) (hgrad m) W) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hbound (m : ℕ) :
      ‖weightedTwoHilbertGradientContraction E g μ hμ h hh φ hφ
        (χ m) (hχ m) (A m) (hA m) (hgrad m) W‖ ≤ Real.sqrt ((2 * A m) * ‖W‖ ^ 2) :=
    (Real.le_sqrt (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (hA m)) (sq_nonneg _))).mpr
      (weightedTwoHilbertGradientContraction_norm_sq_le E g μ hμ h hh φ hφ
        (χ m) (hχ m) (A m) (hA m) (hgrad m) W)
  have ht : Tendsto (fun m => Real.sqrt ((2 * A m) * ‖W‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, Real.sqrt_zero] using
      ((hAtop.const_mul 2).mul_const (‖W‖ ^ 2)).sqrt
  exact squeeze_zero (fun m => norm_nonneg _) hbound ht

end Yau.LeafProofs.L14Aux
