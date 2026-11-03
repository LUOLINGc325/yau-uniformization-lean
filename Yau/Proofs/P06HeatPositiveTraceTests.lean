import Yau.Proofs.P06HeatOrderBounds
import Yau.Proofs.P06TraceHilbertL1

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_unitInterval_compact_smooth_one_near (g : SmoothMetric M)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ η : M.Carrier → ℝ, SmoothFn η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ K, ∀ᶠ y in 𝓝 x, η y = 1 := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨c, _⟩ := hne
    obtain ⟨b, hb⟩ := hK.bddAbove_image (Yau.LeafProofs.L12Aux.continuous_distFrom g c).continuousOn
    let r : ℝ := max b 0 + 1
    have hr : 0 < r := by dsimp only [r]; linarith [le_max_right b 0]
    obtain ⟨η, hη, hcη, hηrange, hηone, _⟩ :=
      Yau.LeafProofs.L18Aux.exists_smooth_compact_cutoff g c hr (show r < r + 1 by linarith)
    refine ⟨η, hη, hcη, hηrange, ?_⟩
    intro x hx
    have hxlt : inducedDistance g.form c x < r := by
      have h := hb ⟨x, hx, rfl⟩
      change inducedDistance g.form c x ≤ b at h
      dsimp only [r]
      linarith [le_max_left b 0]
    filter_upwards [(Yau.LeafProofs.L12Aux.continuous_distFrom g c).continuousAt.eventually
      (Iio_mem_nhds hxlt)] with y hy
    exact hηone y hy.le
  · refine ⟨0, (fun _ => contDiffOn_const), HasCompactSupport.zero, ?_, ?_⟩
    · intro x; exact ⟨le_rfl, zero_le_one⟩
    · intro x hx; exact False.elim (hne ⟨x, hx⟩)

/-- Positive compact tests may be evolved by the actual Hodge heat and
localized again. Their original trace mass never increases. -/
theorem hodgeHeat_localized_positive_test (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (B U : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (h11 : RealOneOne B) (hp : FormLE 0 B)
    (hU : SmoothRealForm U) (hUL : L2RealForm g.form μ U) (t : ℝ) (ht : 0 ≤ t)
    (he : realizeActualForm g μ U hUL = hodgeHeatHilbert g μ hμ 2 t
      (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)))
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηrange : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    SmoothRealForm (multiplyRealForm η U) ∧
      CompactlySupportedRealForm (multiplyRealForm η U) ∧
      RealOneOne (multiplyRealForm η U) ∧ FormLE 0 (multiplyRealForm η U) ∧
      Integrable (formTrace g.form (multiplyRealForm η U)) μ ∧
      (∫ x, formTrace g.form (multiplyRealForm η U) x ∂μ) ≤ ∫ x, formTrace g.form B x ∂μ := by
  let hBL := smooth_compactlySupported_l2RealForm g μ hμ B hB hcB
  have h11U := hodgeHeat_smooth_representative_oneOne g μ hμ hk B U hBL h11 hU hUL t ht he
  have hpU := hodgeHeat_smooth_representative_positive g μ hμ hk hHBC B U hBL h11 hp hU hUL t ht he
  have htr := TraceHilbert.trace_representative_l1 g μ hμ hk B U hB hcB h11 hp hUL h11U t ht he
  have hi := TraceHilbert.compact_trace_integrable g μ hμ U hUL h11U η hη hcη
  refine ⟨smoothRealForm_multiply η U hη hU,
    compactlySupportedRealForm_multiply_scalar η hcη U,
    realOneOne_multiply η U h11U,
    formLE_multiply_nonnegative g.form η (fun x => (hηrange x).1) U hpU, hi, ?_⟩
  calc
    _ ≤ ∫ x, |formTrace g.form U x| ∂μ := integral_mono hi htr.1.abs (fun x => by
      rw [formTrace_multiply_raw g.form η U h11U x]
      have hn := formTrace_nonnegative g.form U h11U hpU x
      rw [abs_of_nonneg hn]
      exact mul_le_of_le_one_left hn (hηrange x).2)
    _ ≤ _ := htr.2

end Yau.NodeProofs.P06Aux
