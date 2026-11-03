import Yau.LeafProofs.L19HeatAnnularGaussianEnergy

/-! True annular cutoff sequences and their actual dominated integral limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- A single dimension constant supplies all compact cutoff radii used
in the actual heat-duality exhaustion. -/
theorem exists_uniform_heat_duality_cutoffs (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M) (o : M.Carrier),
      ∃ η : ℕ → M.Carrier → ℝ,
        (∀ j, SmoothFn (η j) ∧ HasCompactSupport (η j) ∧
          (∀ x, η j x ∈ Icc (0 : ℝ) 1) ∧
          (∀ x, inducedDistance g.form o x ≤ (j : ℝ) + 1 → η j x = 1) ∧
          tsupport (η j) ⊆ distBall g.form o (2 * ((j : ℝ) + 1)) ∧
          (∀ x, scalarGradientPair g.form (η j) (η j) x ≤ A ^ 2 / ((j : ℝ) + 1) ^ 2)) ∧
        ∀ x, Tendsto (fun j => η j x) atTop (𝓝 1) := by
  classical
  obtain ⟨A, hA, hcut⟩ := exists_uniform_annular_scalar_energy_cutoffs n
  refine ⟨A, hA, ?_⟩
  intro M g o
  have hex (j : ℕ) := hcut M g o ((j : ℝ) + 1) (2 * ((j : ℝ) + 1))
    (by positivity) (by have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)
  choose η _hηC hη hcη hrange hone hsupp hE using hex
  refine ⟨η, ?_, ?_⟩
  · intro j
    refine ⟨hη j, hcη j, hrange j, hone j, hsupp j, ?_⟩
    intro x
    have hh := hE j x
    rw [show 2 * ((j : ℝ) + 1) - ((j : ℝ) + 1) = (j : ℝ) + 1 by ring, div_pow] at hh
    exact hh
  · intro x
    have hR : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have heq : (fun j => η j x) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [hR.eventually (eventually_ge_atTop (inducedDistance g.form o x))] with j hj
      exact hone j x hj
    have h₁ : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    exact h₁.congr' heq.symm

/-- The actual Bochner integral passes to a bounded smooth cutoff
exhaustion whenever its scalar input is genuinely integrable. -/
theorem integral_tendsto_smooth_cutoffs (μ : Measure M.Carrier)
    {η : ℕ → M.Carrier → ℝ} (hη : ∀ j, SmoothFn (η j))
    (hrange : ∀ j x, η j x ∈ Icc (0 : ℝ) 1)
    (hlim : ∀ x, Tendsto (fun j => η j x) atTop (𝓝 1))
    {f : M.Carrier → ℝ} (hf : Integrable f μ) :
    Tendsto (fun j => ∫ x, η j x * f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (bound := fun x => |f x|)
  · intro j
    exact ((continuous_of_smoothFn (hη j)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · exact hf.abs
  · intro j
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hrange j x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hrange j x).2)
  · exact ae_of_all _ (fun x => by simpa only [one_mul] using (hlim x).mul_const (f x))

end Yau.LeafProofs.L19Aux
