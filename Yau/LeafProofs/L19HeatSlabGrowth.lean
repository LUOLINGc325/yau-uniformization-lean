import Yau.LeafProofs.L19HeatLocalDuality
import Yau.LeafProofs.L19HeatGaussianTailPointwise

/-! Derived slab growth and pointwise boundary estimates for original heat solutions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Every original positive heat solution has arbitrarily small Gaussian
spatial growth, uniformly on every strictly positive compact time slab. -/
theorem positiveHeatSolution_uniform_slab_growth (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (o : M.Carrier) {s T a : ℝ} (hs : 0 < s) (hsT : s ≤ T) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc s T, ∀ x : M.Carrier,
      u x t ≤ C * Real.exp (a * inducedDistance g.form o x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := positiveHeatSolution_gaussian_growth liYauDifferential g
    hcomplete hK hRic hu o (hs.trans_le hsT) (show 0 < 2 * a by positivity)
  refine ⟨C / s ^ n, div_pos hC (pow_pos hs _), ?_⟩
  intro t ht x
  have hcoef : C / t ^ n ≤ C / s ^ n := by gcongr; exact ht.1
  have hh := hbound t (hs.trans_le ht.1) ht.2 x
  have he : (2 * a) / 2 = a := by ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

/-- Actual dual metric Cauchy--Schwarz, with no coordinate regularity premises. -/
theorem scalarGradientPair_cauchy_sq (h : HermitianField M)
    (f k : M.Carrier → ℝ) (x : M.Carrier) :
    scalarGradientPair h f k x ^ 2 ≤
      scalarGradientPair h f f x * scalarGradientPair h k k x := by
  have hQ := L12Aux.realMetricFn_posDef h x (chartPt x x) (mem_extChartAt_target x)
  have hh := hQ.inv.star_dotProduct_mulVec_mul_le
    (fun i => rDeriv (inChart x f) (chartPt x x) i)
    (fun i => rDeriv (inChart x k) (chartPt x x) i)
  simpa only [scalarGradientPair, chartGradientPair, Matrix.toBilin'_apply',
    star_trivial, pow_two] using hh

/-- A freely tunable Young estimate for each actual cutoff flux. -/
theorem scalarGradientPair_mixed_young (h : HermitianField M)
    (η k : M.Carrier → ℝ) (x : M.Carrier) (u : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |u * scalarGradientPair h η k x| ≤ δ * u ^ 2 +
      (scalarGradientPair h η η x * scalarGradientPair h k k x) / (4 * δ) := by
  let p := scalarGradientPair h η k x
  have hCS := scalarGradientPair_cauchy_sq h η k x
  change p ^ 2 ≤ _ at hCS
  have hY : 4 * δ * |u * p| ≤ 4 * δ ^ 2 * u ^ 2 +
      scalarGradientPair h η η x * scalarGradientPair h k k x := by
    rw [abs_mul]
    nlinarith [sq_nonneg (2 * δ * |u| - |p|), sq_abs u, sq_abs p]
  have hden : 0 < 4 * δ := by positivity
  have he : δ * u ^ 2 +
      (scalarGradientPair h η η x * scalarGradientPair h k k x) / (4 * δ) =
      (4 * δ ^ 2 * u ^ 2 + scalarGradientPair h η η x * scalarGradientPair h k k x) /
        (4 * δ) := by field_simp
  rw [he]
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hY)

/-- One exponential balancing parameter controls both boundary fluxes.
The energies on the right are exactly the quantities in local Caccioppoli. -/
theorem scalarGradientPair_commutator_young (h : HermitianField M)
    (η f k : M.Carrier → ℝ) (x : M.Carrier) {δ : ℝ} (hδ : 0 < δ) :
    |f x * scalarGradientPair h η k x - k x * scalarGradientPair h η f x| ≤
      δ * (f x) ^ 2 + δ⁻¹ * (k x) ^ 2 +
      (δ / 4) * scalarGradientPair h η η x * scalarGradientPair h f f x +
      (1 / (4 * δ)) * scalarGradientPair h η η x * scalarGradientPair h k k x := by
  have hf := scalarGradientPair_mixed_young h η k x (f x) hδ
  have hk := scalarGradientPair_mixed_young h η f x (k x) (inv_pos.mpr hδ)
  have he : (scalarGradientPair h η η x * scalarGradientPair h f f x) /
      (4 * δ⁻¹) = (δ / 4) * scalarGradientPair h η η x * scalarGradientPair h f f x := by
    field_simp
  rw [he] at hk
  have htri : |f x * scalarGradientPair h η k x - k x * scalarGradientPair h η f x| ≤
      |f x * scalarGradientPair h η k x| + |k x * scalarGradientPair h η f x| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (f x * scalarGradientPair h η k x) 0 (k x * scalarGradientPair h η f x)
  have hh := htri.trans (add_le_add hf hk)
  exact hh.trans_eq (by ring)

/-- The integrable domination for a positive original solution paired
with a Gaussian-decaying test is derived uniformly on a compact time slab. -/
theorem positiveHeatSolution_slab_gaussian_product_domination (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u v : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution g.form u) (o : M.Carrier)
    {s T C β : ℝ} (hs : 0 < s) (hsT : s ≤ T) (hC : 0 < C) (hβ : 0 < β)
    (hv : ∀ t ∈ Icc s T, Continuous (fun x => v x t))
    (hdecay : ∀ x t, t ∈ Icc s T → |v x t| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2)) :
    ∃ B : ℝ, 0 < B ∧
      (∀ t ∈ Icc s T, ∀ x, |u x t * v x t| ≤ B * gaussianWeight g o (β / 2) x) ∧
      ∀ t ∈ Icc s T, Integrable (fun x => u x t * v x t) μ := by
  obtain ⟨A, hA, hgrowth⟩ := positiveHeatSolution_uniform_slab_growth g hcomplete hK hRic
    hu o hs hsT (show 0 < β / 2 by positivity)
  have hdom (t : ℝ) (ht : t ∈ Icc s T) (x : M.Carrier) :
      |u x t * v x t| ≤ (A * C) * gaussianWeight g o (β / 2) x := by
    rw [abs_mul, abs_of_pos (hu.2 x t (hs.trans_le ht.1)).1]
    calc
      _ ≤ (A * Real.exp ((β / 2) * inducedDistance g.form o x ^ 2)) *
          (C * Real.exp (-β * inducedDistance g.form o x ^ 2)) :=
        mul_le_mul (hgrowth t ht x) (hdecay x t ht) (abs_nonneg _) (by positivity)
      _ = _ := by
        dsimp only [gaussianWeight]
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 2
        ring
  refine ⟨A * C, mul_pos hA hC, hdom, ?_⟩
  intro t ht
  have hi := (integrable_exp_neg_distance_sq g hK hRic μ hμ o
    (a := β / 2) (by positivity)).const_mul (A * C)
  apply hi.mono' (((continuous_of_smoothFn
    (positiveHeatSolution_slice g.form hu (hs.trans_le ht.1))).mul (hv t ht)).aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, gaussianWeight, neg_mul] using hdom t ht x)

end Yau.LeafProofs.L19Aux
