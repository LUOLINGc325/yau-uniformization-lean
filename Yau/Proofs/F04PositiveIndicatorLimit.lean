import Yau.Proofs.F04PositiveIndicator
import Yau.Proofs.F04UniformOperatorLimit

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem positiveIndicator_tendsto_of_ne_zero {ι : Type*} {l : Filter ι}
    (f : ι → ℝ) (s : ℝ) (hf : Tendsto f l (𝓝 s)) (hs : s ≠ 0) :
    Tendsto (fun j => positiveIndicator (f j)) l (𝓝 (positiveIndicator s)) := by
  by_cases hp : 0 < s
  · have he : (fun j => positiveIndicator (f j)) =ᶠ[l] (fun _ => (1 : ℝ)) := by
      filter_upwards [hf.eventually (lt_mem_nhds hp)] with j hj
      exact ite_eq_left hj
    change Tendsto (fun j => positiveIndicator (f j)) l (𝓝 (if 0 < s then (1 : ℝ) else 0))
    rw [ite_eq_left hp]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  · have hn : s < 0 := lt_of_le_of_ne (le_of_not_gt hp) hs
    have he : (fun j => positiveIndicator (f j)) =ᶠ[l] (fun _ => (0 : ℝ)) := by
      filter_upwards [hf.eventually (gt_mem_nhds hn)] with j hj
      exact ite_eq_right (not_lt.mpr hj.le)
    change Tendsto (fun j => positiveIndicator (f j)) l (𝓝 (if 0 < s then (1 : ℝ) else 0))
    rw [ite_eq_right hp]
    exact (tendsto_congr' he).mpr tendsto_const_nhds

/-- Strong convergence survives the discontinuous indicator because the
limiting actual differential vanishes on the scalar zero level. -/
theorem positiveFormMultiplier_tendsto_on_zero_level
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : ℕ → Lp ℝ 2 μ) (f₀ : Lp ℝ 2 μ) (hf : Tendsto f atTop (𝓝 f₀))
    (A : RealForm M 1) (hA : L2RealForm g.form μ A)
    (hAzero : ∀ᵐ x ∂μ, f₀ x = 0 → A x = 0)
    (a : ℕ → L2FormHilbert g μ 1)
    (ha : Tendsto a atTop (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection A hA)))) :
    Tendsto (fun j => positiveFormMultiplier g μ (f j) (a j)) atTop
      (𝓝 (positiveFormMultiplier g μ f₀ (realizeL2Form g μ (L2FormSpace.ofSection A hA)))) := by
  apply uniformly_bounded_operators_apply_tendsto
    (fun j => positiveFormMultiplier g μ (f j)) 1
    (fun j => multiplyL2FormHilbert_opNorm_le g μ _ _ 1 zero_le_one _) a _ _ ha
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hms⟩ := (tendstoInMeasure_of_tendsto_Lp (hf.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply bounded_form_multipliers_tendsto g μ A hA
    (fun j x => positiveIndicator (f (ns (ms j)) x)) (fun x => positiveIndicator (f₀ x))
    (fun j => positiveIndicator_aestronglyMeasurable μ (f (ns (ms j))))
    (positiveIndicator_aestronglyMeasurable μ f₀) 1 zero_le_one
    (fun j x => positiveIndicator_abs_le (f (ns (ms j)) x)) (fun x => positiveIndicator_abs_le (f₀ x))
  filter_upwards [hms, hAzero] with x hx hz
  by_cases hs : f₀ x = 0
  · have hnorm : formNormSq g.form A x = 0 := by
      rw [formNormSq_congr_at g.form (A' := (0 : RealForm M 1)) (hz hs), formNormSq_zero]
      rfl
    simp only [hnorm, mul_zero]
    exact tendsto_const_nhds
  · have ht := ((positiveIndicator_tendsto_of_ne_zero (fun j => f (ns (ms j)) x)
        (f₀ x) hx hs).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => positiveIndicator (f₀ x)) atTop
        (𝓝 (positiveIndicator (f₀ x))))).pow 2
    simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul] using
      ht.mul_const (formNormSq g.form A x)

end Yau.F04Proof
