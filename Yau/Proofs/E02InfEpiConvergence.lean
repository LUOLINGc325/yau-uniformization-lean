import Yau.Proofs.E02InfConvolution

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E]

/-- The actual minimizing sources converge to the same evaluation point.
The source compactum and its upper bound are fixed before kappa varies. -/
theorem compactInfConvolution_sources_tendsto
    (K : Set E) (v : E → ℝ) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκlim : Tendsto κ atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (q a : ℕ → E) (q₀ : E)
    (hqK : ∀ j, q j ∈ K) (haK : ∀ j, a j ∈ K)
    (hqM : ∀ j, v (q j) ≤ M) (hqLim : Tendsto q atTop (𝓝 q₀))
    (hEq : ∀ j, compactInfConvolution K v (κ j) (q j) =
      v (a j)+‖q j-a j‖^2/(2*κ j)) :
    Tendsto a atTop (𝓝 q₀) := by
  have hBound : ∀ j, ‖q j-a j‖ ≤ Real.sqrt (2*κ j*M) := by
    intro j
    exact (compactInfConvolution_source_displacement K v hv0 (hκ j) hM
      (q j) (a j) (hqK j) (haK j) (hqM j) (hEq j)).2
  have hScale : Tendsto (fun j => 2*κ j*M) atTop (𝓝 (2*0*M)) :=
    (tendsto_const_nhds.mul hκlim).mul tendsto_const_nhds
  have hSqrt : Tendsto (fun j => Real.sqrt (2*κ j*M)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,Real.sqrt_zero,Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hScale
  have hNorm : Tendsto (fun j => ‖q j-a j‖) atTop (𝓝 0) :=
    squeeze_zero (fun j => norm_nonneg (q j-a j)) hBound hSqrt
  apply hqLim.congr_dist
  simpa only [dist_eq_norm] using hNorm

/-- Genuine epigraph convergence, in an eventual lower-bound form that
needs no conditional real liminf. All minima are constructed from K. -/
theorem compactInfConvolution_lower_limit
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκlim : Tendsto κ atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (q : ℕ → E) (q₀ : E) (hq₀ : q₀ ∈ K)
    (hqK : ∀ j, q j ∈ K) (hqM : ∀ j, v (q j) ≤ M)
    (hqLim : Tendsto q atTop (𝓝 q₀)) :
    ∀ r < v q₀, ∀ᶠ j in atTop, r ≤ compactInfConvolution K v (κ j) (q j) := by
  choose a haK hEq _hMin using fun j => compactInfConvolution_attained K v hK hne hv (κ j) (q j)
  have haLim : Tendsto a atTop (𝓝 q₀) :=
    compactInfConvolution_sources_tendsto K v hv0 κ hκ hκlim hM q a q₀ hqK haK hqM hqLim hEq
  have haWithin : Tendsto a atTop (𝓝[K] q₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨haLim,Eventually.of_forall haK⟩
  intro r hr
  filter_upwards [haWithin.eventually (hv q₀ hq₀ r hr)] with j hj
  apply hj.le.trans
  rw [hEq j]
  have hκj : 0 < κ j := hκ j
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity))

end Yau.NodeProofs.E02Aux
