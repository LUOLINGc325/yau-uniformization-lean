import Yau.Proofs.P06HodgeSpectral

/-! The original L² initial and energy clauses from the actual realization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal

namespace Yau.NodeProofs.P06Aux.L2HeatExistence
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem actualForm_distanceSq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    formL2DistanceSq g.form μ A B =
      ENNReal.ofReal (‖realizeActualForm g μ A hA - realizeActualForm g μ B hB‖ ^ 2) :=
  (realizeL2Form_distanceSq g μ (L2FormSpace.ofSection A hA)
    (L2FormSpace.ofSection B hB)).symm

theorem actualForm_lintegral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    (∫⁻ x, ENNReal.ofReal (formNormSq g.form A x) ∂μ) =
      ENNReal.ofReal (‖realizeActualForm g μ A hA‖ ^ 2) := by
  rw [realizeActualForm_norm_sq, ofReal_integral_eq_lintegral_ofReal
    (formNormSq_integrable g μ A hA) (ae_of_all _ (fun x => formNormSq_nonneg _ _ x))]

theorem heatRealization_initial (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (U : ℝ → RealForm M k)
    (hU : ∀ t, 0 < t → ∃ hUt : L2RealForm g.form μ (U t),
      realizeActualForm g μ (U t) hUt =
        hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ A hA)) :
    Tendsto (fun t => formL2DistanceSq g.form μ (U t) A) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := (hodgeHeatHilbert_tendsto_zero g μ hμ k (realizeActualForm g μ A hA)).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp ht
  have hp : Tendsto (fun t : ℝ =>
      ‖hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ A hA) -
        realizeActualForm g μ A hA‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hn.pow 2
  have he := ENNReal.tendsto_ofReal hp
  rw [ENNReal.ofReal_zero] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨hUt, hr⟩ := hU t ht
  rw [actualForm_distanceSq g μ (U t) A hUt hA, hr]

theorem heatRealization_lintegral_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (U : ℝ → RealForm M k)
    (hU : ∀ t, 0 < t → ∃ hUt : L2RealForm g.form μ (U t),
      realizeActualForm g μ (U t) hUt =
        hodgeHeatHilbert g μ hμ k t (realizeActualForm g μ A hA)) :
    ∀ t, 0 < t → (∫⁻ x, ENNReal.ofReal (formNormSq g.form (U t) x) ∂μ) ≤
      ENNReal.ofReal (‖realizeActualForm g μ A hA‖ ^ 2) := by
  intro t ht
  obtain ⟨hUt, hr⟩ := hU t ht
  rw [actualForm_lintegral g μ (U t) hUt, hr]
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (hodgeHeatHilbert_bound g μ hμ k t _) 2

end Yau.NodeProofs.P06Aux.L2HeatExistence
