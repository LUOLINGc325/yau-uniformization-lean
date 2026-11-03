import Yau.LeafProofs.L19HeatWeightedMass
import Yau.LeafProofs.L19HeatC0Initial
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Weighted compact approximation and compact-uniform initial continuity.
These estimates never use the unweighted total mass of the heat kernel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- Domination by a genuinely integrable weighted mass constructs the product
integral and bounds its absolute value. -/
theorem weighted_trace_product_bound (μ : Measure M.Carrier)
    {u w f : M.Carrier → ℝ} {D : ℝ}
    (hu : ∀ x, 0 ≤ u x) (hi : Integrable (fun x => u x * w x) μ)
    (hm : AEStronglyMeasurable (fun x => u x * f x) μ)
    (hb : ∀ x, |f x| ≤ D * w x) :
    Integrable (fun x => u x * f x) μ ∧
      |∫ x, u x * f x ∂μ| ≤ D * ∫ x, u x * w x ∂μ := by
  have hd : ∀ᵐ x ∂μ, ‖u x * f x‖ ≤ D * (u x * w x) := by
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hu x)]
    calc
      u x * |f x| ≤ u x * (D * w x) := mul_le_mul_of_nonneg_left (hb x) (hu x)
      _ = D * (u x * w x) := by ring
  refine ⟨(hi.const_mul D).mono' hm hd, ?_⟩
  have h := norm_integral_le_of_norm_le (hi.const_mul D) hd
  simpa only [Real.norm_eq_abs, integral_const_mul] using h

/-- On the proper metric underlying the original manifold, joint continuity
on a compact time interval and a uniform vanishing radial tail give uniform
initial continuity in all of space. -/
theorem continuousOn_radial_tail_uniform_initial (g : SmoothMetric M) (o : M.Carrier)
    {q : M.Carrier → ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn (fun p : M.Carrier × ℝ => q p.1 p.2) (univ ×ˢ Icc 0 T))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x t,
      t ∈ Icc 0 T → R ≤ inducedDistance g.form o x → |q x t| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x, |q x s - q x 0| < ε := by
  let := inducedMetricSpace g
  intro ε hε
  obtain ⟨R, _hR, hfar⟩ := htail (ε / 4) (by positivity)
  let K := {x : M.Carrier | inducedDistance g.form o x ≤ R}
  have hK : IsCompact K := isCompact_inducedDistance_sublevel g o R
  have hc' : ContinuousOn (fun p : ℝ × M.Carrier => q p.2 p.1) (Icc 0 T ×ˢ K) := by
    exact hc.comp continuous_swap.continuousOn (fun p hp => ⟨mem_univ _, hp.1⟩)
  have hu : TendstoUniformlyOn (fun t x => q x t) (fun x => q x 0) (𝓝[Icc 0 T] 0) K :=
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc').tendstoUniformlyOn
      ⟨le_rfl, hT.le⟩
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 T] 0 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hT]
    exact nhdsWithin_mono 0 (fun t ht => show 0 ≤ t from (show 0 < t from ht).le)
  have he := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (by positivity)).filter_mono hle
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [he, hpos, hsmall] with s hs hs0 hsT
  intro x
  by_cases hx : x ∈ K
  · have hxsmall : |q x s - q x 0| < ε / 2 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hs x hx
    linarith only [hxsmall, hε]
  · have hxR : R ≤ inducedDistance g.form o x := le_of_lt (lt_of_not_ge hx)
    have h1 := hfar x s ⟨hs0.le, hsT.le⟩ hxR
    have h0 := hfar x 0 ⟨le_rfl, hT.le⟩ hxR
    have htri := abs_sub (q x s) (q x 0)
    linarith only [h1, h0, htri, hε]

/-- The original compact-test delta trace extends to continuous tests whose
ratio to one fixed Gaussian vanishes at infinity.  The only mass bound is
for that Gaussian, and every product integral used below is constructed. -/
theorem scalarHeatKernel_weighted_trace_of_radial_decay
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H) (y o : M.Carrier)
    {a T B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (hmass : ∀ s : ℝ, 0 < s → s ≤ T →
      Integrable (fun x => H s x y * gaussianWeight g o a x) μ ∧
      (∫ x, H s x y * gaussianWeight g o a x ∂μ) ≤ B)
    {f : M.Carrier → ℝ} (hf : Continuous f)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x,
      R ≤ inducedDistance g.form o x → |f x / gaussianWeight g o a x| < ε) :
    Tendsto (fun s : ℝ => ∫ x, H s x y * f x ∂μ) (𝓝[>] 0) (𝓝 (f y)) := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  let w := gaussianWeight g o a
  have hw : ∀ x, 0 < w x := gaussianWeight_pos g o a
  have hwc : Continuous w := gaussianWeight_continuous g o a
  have hqc : Continuous (fun x => f x / w x) := hf.div hwc (fun x => (hw x).ne')
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsum : 0 < B + w y := add_pos hB (hw y)
  let δ := ε / (4 * (B + w y))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (B + w y) = ε / 4 := by
    dsimp only [δ]
    field_simp [hsum.ne']
  obtain ⟨k, hk⟩ := exists_uniform_compact_core_of_radial_decay g μ hμ o hqc hdecay hδ
  let F : M.Carrier → ℝ := fun x => w x * k x
  have hFc : Continuous F := hwc.mul (continuous_of_smoothFn k.2.1)
  have hFs : HasCompactSupport F := k.2.2.mul_left
  have herr (x : M.Carrier) : |f x - F x| ≤ δ * w x := by
    have heq : f x - F x = w x * (f x / w x - k x) := by
      dsimp only [F]
      field_simp [(hw x).ne']
    rw [heq, abs_mul, abs_of_pos (hw x), mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hk x).le (hw x).le
  have ht := Metric.tendsto_nhds.mp (hH.2.2 F hFc hFs y) (ε / 2) (by positivity)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht, hpos, hsmall] with s hs hs0 hsT
  have huc : Continuous (fun x => H s x y) :=
    continuous_of_smoothFn (smoothSpaceTime_slice (hH.1 y).1 hs0)
  have hik : Integrable (fun x => H s x y * F x) μ :=
    (huc.mul hFc).integrable_of_hasCompactSupport hFs.mul_left
  obtain ⟨hie, he⟩ := weighted_trace_product_bound μ
    (fun x => ((hH.1 y).2 x s hs0).1.le) (hmass s hs0 hsT.le).1
    (huc.mul (hf.sub hFc)).aestronglyMeasurable herr
  have hif : Integrable (fun x => H s x y * f x) μ := by
    apply (hie.add hik).congr
    exact ae_of_all _ (fun x => by dsimp; ring)
  have hsub : (∫ x, H s x y * f x ∂μ) - (∫ x, H s x y * F x ∂μ) =
      ∫ x, H s x y * (f x - F x) ∂μ := by
    rw [← integral_sub hif hik]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have heB : |(∫ x, H s x y * f x ∂μ) - (∫ x, H s x y * F x ∂μ)| ≤ δ * B := by
    rw [hsub]
    exact he.trans (mul_le_mul_of_nonneg_left (hmass s hs0 hsT.le).2 hδ.le)
  have hy : |F y - f y| ≤ δ * w y := by rw [abs_sub_comm]; exact herr y
  have htri1 := abs_sub_le (∫ x, H s x y * f x ∂μ) (∫ x, H s x y * F x ∂μ) (f y)
  have htri2 := abs_sub_le (∫ x, H s x y * F x ∂μ) (F y) (f y)
  rw [Real.dist_eq] at hs ⊢
  nlinarith only [htri1, htri2, hs, heB, hy, hδeq, hε]

end Yau.LeafProofs.L19Aux
