import Yau.Proofs.F04LpParameterDerivative

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

theorem finiteLpCurve_hasDerivWithinAt
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f d : ℝ → X → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) (hd : ∀ t, MemLp (d t) 2 μ)
    {S : ℝ} (_hS : 0 < S) (C : ℝ) (_hC : 0 ≤ C)
    (hder : ∀ᵐ x ∂μ, ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun s => f s x) (d t x) (Icc 0 S) t)
    (hdb : ∀ᵐ x ∂μ, ∀ t ∈ Icc 0 S, ‖d t x‖ ≤ C)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    HasDerivWithinAt (fun s => (hf s).toLp (f s)) ((hd t).toLp (d t)) (Icc 0 S) t := by
  apply hasDerivWithinAt_toLp_of_dominated_slopes μ f hf (d t) (hd t) (Icc 0 S) t
    (hder.mono fun _ hx => hx t ht) (fun _ => C) (memLp_const C)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hst : s ≠ t := by simpa only [mem_singleton_iff] using hs.2
  filter_upwards [hder, hdb] with x hx hb
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q hq => hx q hq) (fun q hq => hb q hq) (convex_Icc (0 : ℝ) S) ht hs.1
  rw [slope_def_module, norm_smul, norm_inv]
  calc
    ‖s - t‖⁻¹ * ‖f s x - f t x‖ ≤ ‖s - t‖⁻¹ * (C * ‖s - t‖) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (norm_nonneg _))
    _ = C := by
      rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hst)), mul_one]

/-- A finite-domain scalar curve with actual continuous bounded pointwise
derivative is C1 in the genuine L2 norm, including both closed-time faces. -/
theorem finiteLpCurve_contDiffOn_one
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f d : ℝ → X → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) (hd : ∀ t, MemLp (d t) 2 μ)
    {S : ℝ} (hS : 0 < S) (C : ℝ) (hC : 0 ≤ C)
    (hder : ∀ᵐ x ∂μ, ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun s => f s x) (d t x) (Icc 0 S) t)
    (hdb : ∀ᵐ x ∂μ, ∀ t ∈ Icc 0 S, ‖d t x‖ ≤ C)
    (hdc : ∀ᵐ x ∂μ, ContinuousOn (fun t => d t x) (Icc 0 S)) :
    ContDiffOn ℝ 1 (fun t => (hf t).toLp (f t)) (Icc 0 S) := by
  have hD : ContinuousOn (fun t => (hd t).toLp (d t)) (Icc 0 S) := by
    intro t ht
    apply toLp_tendsto_of_dominated_differences μ d hd (d t) (hd t)
      (fun _ => 2 * C) (memLp_const (2 * C))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [hdb] with x hx
      exact (norm_sub_le _ _).trans (by linarith [hx s hs, hx t ht])
    · filter_upwards [hdc] with x hx
      exact hx t ht
  have hF := finiteLpCurve_hasDerivWithinAt μ f d hf hd hS C hC hder hdb
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hS)).mpr
  refine ⟨fun t ht => (hF t ht).differentiableWithinAt, hD.congr ?_⟩
  intro t ht
  exact (hF t ht).derivWithin (uniqueDiffOn_Icc hS t ht)

end Yau.F04Proof
