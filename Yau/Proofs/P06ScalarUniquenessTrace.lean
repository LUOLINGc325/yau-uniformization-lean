import Yau.Blueprint.HeatSmoothing
import Yau.LeafProofs.L19HeatLocalCaccioppoli

/-! Compact energy consequences of the original continuous-initial scalar
heat class.  These lemmas concern arbitrary classical solutions. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Subtracting two solutions retains the actual PDE and the compact uniform
initial trace, including when the common initial datum is only continuous. -/
theorem continuousInitialHeat_sub {g : HermitianField M}
    {f h : M.Carrier → ℝ} {u v : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g f u)
    (hv : IsContinuousInitialScalarHeat g h v) :
    IsContinuousInitialScalarHeat g (fun x => f x - h x)
      (fun t x => u t x - v t x) := by
  refine ⟨fun x => by change u 0 x - v 0 x = f x - h x; rw [hu.1, hv.1], fun a => (hu.2.1 a).sub (hv.2.1 a), ?_, ?_, ?_⟩
  · intro x t ht
    have hlin := laplacian_linear_combination g
      (Yau.LeafProofs.L19Aux.smoothSpaceTime_slice hu.2.1 ht)
      (Yau.LeafProofs.L19Aux.smoothSpaceTime_slice hv.2.1 ht) 1 (-1) x
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hlin
    rw [hlin]
    exact (hu.2.2.1 x t ht).sub (hv.2.2.1 x t ht)
  · intro T hT
    obtain ⟨B, hB, hb⟩ := hu.2.2.2.1 T hT
    obtain ⟨C, hC, hc⟩ := hv.2.2.2.1 T hT
    exact ⟨B + C, add_nonneg hB hC, fun x t ht htT =>
      (abs_sub _ _).trans (add_le_add (hb x t ht htT) (hc x t ht htT))⟩
  · intro K hK ε hε
    obtain ⟨δ, hδ, hd⟩ := hu.2.2.2.2 K hK (ε / 2) (by positivity)
    obtain ⟨γ, hγ, hg⟩ := hv.2.2.2.2 K hK (ε / 2) (by positivity)
    refine ⟨min δ γ, lt_min hδ hγ, ?_⟩
    intro t ht htm x hx
    have ha := hd t ht (lt_of_lt_of_le htm (min_le_left _ _)) x hx
    have hb := hg t ht (lt_of_lt_of_le htm (min_le_right _ _)) x hx
    calc
      |u t x - v t x - (f x - h x)| = |(u t x - f x) - (v t x - h x)| := by congr 1; ring
      _ ≤ |u t x - f x| + |v t x - h x| := abs_sub _ _
      _ ≤ ε := by linarith

/-- The original compact uniform initial trace gives pointwise convergence
from positive time, without any differentiability of the datum. -/
theorem continuousInitialHeat_tendsto {g : HermitianField M}
    {f : M.Carrier → ℝ} {u : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g f u) (x : M.Carrier) :
    Tendsto (fun t => u t x) (𝓝[>] 0) (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hu.2.2.2.2 {x} (isCompact_singleton) (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  rw [Real.dist_eq]
  exact (hd t ht.1 ht.2 x (mem_singleton x)).trans_lt (by linarith)

/-- Every compactly localized squared energy has its genuine zero initial
limit.  Only the original finite-time bound and continuous trace are used. -/
theorem continuousInitialHeat_cutoff_energy_tendsto_zero
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {u : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g.form 0 u)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηbound : ∀ x, |η x| ≤ 1) :
    Tendsto (fun t => ∫ x, η x ^ 2 * u t x ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0) := by
  letI : IsLocallyFiniteMeasure μ := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  obtain ⟨B, hB, hb⟩ := hu.2.2.2.1 1 zero_lt_one
  let b : M.Carrier → ℝ := (tsupport η).indicator (fun _ => B ^ 2)
  have hbi : Integrable b μ :=
    (integrableOn_const hcη.isCompact.measure_ne_top).integrable_indicator (isClosed_tsupport η).measurableSet
  have him : ∀ᶠ t in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x => η x ^ 2 * u t x ^ 2) μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (Yau.LeafProofs.L18Aux.continuous_of_smoothFn
      (smoothFn_mul (smoothFn_pow hη 2)
        (smoothFn_pow (Yau.LeafProofs.L19Aux.smoothSpaceTime_slice hu.2.1 ht) 2))).aestronglyMeasurable
  have hib : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖η x ^ 2 * u t x ^ 2‖ ≤ b x := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact ae_of_all _ (fun x => by
      by_cases hx : x ∈ tsupport η
      · have heta : η x ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (η x)) (hηbound x) 2
        have hut : u t x ^ 2 ≤ B ^ 2 := by
          have hh := hb x t ht.1 ht.2.le
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u t x)) hh 2
        change ‖η x ^ 2 * u t x ^ 2‖ ≤ (tsupport η).indicator (fun _ => B ^ 2) x
        rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact (mul_le_of_le_one_left (sq_nonneg _) heta).trans hut
      · simp [b, hx, image_eq_zero_of_notMem_tsupport hx])
  have hil : ∀ᵐ x ∂μ, Tendsto (fun t => η x ^ 2 * u t x ^ 2)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    exact ae_of_all _ (fun x => by
      simpa only [Pi.zero_apply, zero_pow (by omega : 2 ≠ 0), mul_zero] using
        (continuousInitialHeat_tendsto hu x).pow 2 |>.const_mul (η x ^ 2))
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence b him hib hbi hil

end Yau.NodeProofs.P06Aux
