import Yau.LeafProofs.L19WeightedTraceApprox

/-! The delta trace of the original scalar heat kernel on genuinely moving,
Gaussian-decaying tests.  Uniform weighted mass is proved internally. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- Splitting the exponent of the actual metric Gaussian. -/
theorem gaussianWeight_split_exponent (g : SmoothMetric M) (o x : M.Carrier) (a b : ℝ) :
    gaussianWeight g o b x = gaussianWeight g o (b - a) x * gaussianWeight g o a x := by
  unfold gaussianWeight
  rw [← Real.exp_add]
  congr 1
  ring

/-- Gaussian domination improves to vanishing domination after division by
a slower Gaussian. -/
theorem gaussianWeight_quotient_bound (g : SmoothMetric M) (o : M.Carrier)
    {f : M.Carrier → ℝ} {a b C : ℝ}
    (hb : ∀ x, |f x| ≤ C * gaussianWeight g o b x) (x : M.Carrier) :
    |f x / gaussianWeight g o a x| ≤ C * gaussianWeight g o (b - a) x := by
  rw [abs_div, abs_of_pos (gaussianWeight_pos g o a x),
    div_le_iff₀ (gaussianWeight_pos g o a x)]
  have h := hb x
  rw [gaussianWeight_split_exponent g o x a b] at h
  simpa only [mul_assoc] using h

/-- A uniform Gaussian envelope gives a uniform vanishing radial tail. -/
theorem gaussian_dominated_uniform_radial_tail (g : SmoothMetric M) (o : M.Carrier)
    {q : M.Carrier → ℝ → ℝ} {T C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hbound : ∀ x t, t ∈ Icc 0 T → |q x t| ≤ C * gaussianWeight g o b x) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x t,
      t ∈ Icc 0 T → R ≤ inducedDistance g.form o x → |q x t| < ε := by
  intro ε hε
  obtain ⟨R, hR, hfar⟩ := gaussianWeight_small_far g o hb (div_pos hε hC)
  refine ⟨R, hR, ?_⟩
  intro x t ht hx
  have h := mul_lt_mul_of_pos_left (hfar x hx) hC
  have heq : C * (ε / C) = ε := by field_simp
  rw [heq] at h
  exact (hbound x t ht).trans_lt h

/-- The original kernel has its delta trace on every smooth moving test with
a uniform Gaussian envelope on a genuine interval containing time zero.
All products on the time slab are actual integrable functions. -/
theorem scalarHeatKernel_moving_gaussian_trace_data (hn : 0 < n)
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H) (y o : M.Carrier)
    {I : Set ℝ} (hI : IsOpen I) {v : M.Carrier → ℝ → ℝ}
    (hv : SmoothSpaceTime v I) {T C β : ℝ} (hT : 0 < T)
    (hslab : Icc 0 T ⊆ I) (hC : 0 < C) (hβ : 0 < β)
    (hdecay : ∀ x t, t ∈ Icc 0 T →
      |v x t| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2)) :
    (∀ s : ℝ, 0 < s → s ≤ T → Integrable (fun x => H s x y * v x s) μ) ∧
      Tendsto (fun s : ℝ => ∫ x, H s x y * v x s ∂μ) (𝓝[>] 0) (𝓝 (v y 0)) := by
  let a := β / 2
  let w := gaussianWeight g o a
  have ha : 0 < a := by dsimp [a]; positivity
  have hba : 0 < β - a := by dsimp [a]; linarith
  have hw : ∀ x, 0 < w x := gaussianWeight_pos g o a
  have h00 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hnorm (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |v x t| ≤ C * gaussianWeight g o β x := by
    simpa only [gaussianWeight, neg_mul] using hdecay x t ht
  have hbound (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) : |v x t| ≤ C * w x := by
    have hwle : gaussianWeight g o β x ≤ w x := by
      dsimp only [w, gaussianWeight]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hba.le (sq_nonneg (inducedDistance g.form o x))]
    exact (hnorm x t ht).trans (mul_le_mul_of_nonneg_left hwle hC.le)
  obtain ⟨B, hB, hmass⟩ := positiveHeatSolution_uniform_gaussian_weighted_mass hn g hcomplete hK hRic
    μ hμ (hH.1 y) o ha hT
  have hi (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
      Integrable (fun x => H s x y * v x t) μ := by
    have huc := continuous_of_smoothFn (smoothSpaceTime_slice (hH.1 y).1 hs)
    have hvc := continuous_of_smoothFn (smoothSpaceTime_slice hv (hslab ht))
    exact (weighted_trace_product_bound μ (fun x => ((hH.1 y).2 x s hs).1.le)
      (hmass s hs hsT).1 (huc.mul hvc).aestronglyMeasurable
      (fun x => hbound x t ht)).1
  refine ⟨fun s hs hsT => hi s hs hsT s ⟨hs.le, hsT⟩, ?_⟩
  let q : M.Carrier → ℝ → ℝ := fun x t => v x t / w x
  have hqbound (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |q x t| ≤ C * gaussianWeight g o (β - a) x :=
    gaussianWeight_quotient_bound g o (fun x => hnorm x t ht) x
  have hqtail := gaussian_dominated_uniform_radial_tail g o hC hba hqbound
  have hqcont : ContinuousOn (fun p : M.Carrier × ℝ => q p.1 p.2) (univ ×ˢ Icc 0 T) := by
    intro p hp
    exact ((LocalTime.smoothSpaceTime_continuousAt hI hv p.1 (hslab hp.2)).div
      ((gaussianWeight_continuous g o a).continuousAt.comp continuousAt_fst)
      (hw p.1).ne').continuousWithinAt
  have hf0 : Continuous (fun x => v x 0) :=
    continuous_of_smoothFn (smoothSpaceTime_slice hv (hslab h00))
  have ht0 : Tendsto (fun s : ℝ => ∫ x, H s x y * v x 0 ∂μ) (𝓝[>] 0) (𝓝 (v y 0)) := by
    apply scalarHeatKernel_weighted_trace_of_radial_decay g μ hμ hH y o hT hB hmass hf0
    intro ε hε
    obtain ⟨R, hR, hfar⟩ := hqtail ε hε
    exact ⟨R, hR, fun x hx => hfar x 0 h00 hx⟩
  have hquniform := continuousOn_radial_tail_uniform_initial g o hT hqcont hqtail
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * B = ε / 2 := by dsimp only [δ]; field_simp
  have he := hquniform δ hδ
  have ht := Metric.tendsto_nhds.mp ht0 (ε / 2) (by positivity)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, ht, hpos, hsmall] with s hs ht hs0 hsT
  have herr (x : M.Carrier) : |v x s - v x 0| ≤ δ * w x := by
    have heq : v x s - v x 0 = w x * (q x s - q x 0) := by
      dsimp only [q]
      field_simp [(hw x).ne']
    rw [heq, abs_mul, abs_of_pos (hw x), mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hs x).le (hw x).le
  have huc := continuous_of_smoothFn (smoothSpaceTime_slice (hH.1 y).1 hs0)
  have hvc := continuous_of_smoothFn (smoothSpaceTime_slice hv (hslab ⟨hs0.le, hsT.le⟩))
  have hdiff := (weighted_trace_product_bound μ (fun x => ((hH.1 y).2 x s hs0).1.le)
    (hmass s hs0 hsT.le).1 (huc.mul (hvc.sub hf0)).aestronglyMeasurable herr).2
  have hsub : (∫ x, H s x y * v x s ∂μ) - (∫ x, H s x y * v x 0 ∂μ) =
      ∫ x, H s x y * (v x s - v x 0) ∂μ := by
    rw [← integral_sub (hi s hs0 hsT.le s ⟨hs0.le, hsT.le⟩) (hi s hs0 hsT.le 0 h00)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hdiffB : |(∫ x, H s x y * v x s ∂μ) - (∫ x, H s x y * v x 0 ∂μ)| ≤ ε / 2 := by
    rw [hsub]
    exact (hdiff.trans (mul_le_mul_of_nonneg_left (hmass s hs0 hsT.le).2 hδ.le)).trans_eq hδeq
  have htri := abs_sub_le (∫ x, H s x y * v x s ∂μ) (∫ x, H s x y * v x 0 ∂μ) (v y 0)
  rw [Real.dist_eq] at ht ⊢
  linarith only [htri, hdiffB, ht]

/-- Continuous compact-test initial traces of the original positive kernel
extend to genuinely Gaussian-decaying moving tests at time zero. -/
theorem scalarHeatKernel_moving_gaussian_trace (hn : 0 < n)
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H) (y o : M.Carrier)
    {I : Set ℝ} (hI : IsOpen I) {v : M.Carrier → ℝ → ℝ}
    (hv : SmoothSpaceTime v I) {T C β : ℝ} (hT : 0 < T)
    (hslab : Icc 0 T ⊆ I) (hC : 0 < C) (hβ : 0 < β)
    (hdecay : ∀ x t, t ∈ Icc 0 T →
      |v x t| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2)) :
    Tendsto (fun s : ℝ => ∫ x, H s x y * v x s ∂μ) (𝓝[>] 0) (𝓝 (v y 0)) :=
  (scalarHeatKernel_moving_gaussian_trace_data hn g hcomplete hK hRic μ hμ hH y o
    hI hv hT hslab hC hβ hdecay).2

end Yau.LeafProofs.L19Aux
