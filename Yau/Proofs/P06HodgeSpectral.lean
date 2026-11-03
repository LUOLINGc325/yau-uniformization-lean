import Yau.Proofs.P06SpectralReal
import Yau.Proofs.P06HodgeOperator

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Canonical complete real Hodge heat, with exactly the paper generator
`-□/2`. The bounded resolvent is the actual `(1+□)⁻¹`, hence the time `t/2`. -/
def hodgeHeatHilbert (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  Spectral.realHeat (hodgeResolventOne g μ hμ k) (hodgeResolventOne_symmetric g μ hμ k)
    (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
    (hodgeResolventOne_injective g μ hμ k) (t / 2)

def hodgeHeatHilbertInverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  Spectral.realHeatInverse (hodgeResolventOne g μ hμ k) (hodgeResolventOne_symmetric g μ hμ k)
    (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
    (hodgeResolventOne_injective g μ hμ k) (t / 2)

@[simp] theorem hodgeHeatHilbert_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) : hodgeHeatHilbert g μ hμ k 0 = 1 := by
  simp only [hodgeHeatHilbert, zero_div, Spectral.realHeat_zero]

theorem hodgeHeatHilbert_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) (f : L2FormHilbert g μ k) :
    ‖hodgeHeatHilbert g μ hμ k t f‖ ≤ ‖f‖ :=
  Spectral.realHeat_norm_le (hodgeResolventOne g μ hμ k) (hodgeResolventOne_symmetric g μ hμ k)
    (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
    (hodgeResolventOne_injective g μ hμ k) (t / 2) f

theorem hodgeHeatHilbert_factor (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    hodgeHeatHilbert g μ hμ k t = hodgeResolventOne g μ hμ k * hodgeHeatHilbertInverse g μ hμ k t :=
  Spectral.realHeat_factor (hodgeResolventOne g μ hμ k) (hodgeResolventOne_symmetric g μ hμ k)
    (hodgeResolventOne_positive g μ hμ k) (hodgeResolventOne_bound g μ hμ k)
    (hodgeResolventOne_injective g μ hμ k) (by positivity : 0 < t / 2)

theorem hodgeHeatHilbert_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (t : ℝ) :
    (hodgeHeatHilbert g μ hμ k t).IsSymmetric :=
  Spectral.realHeat_symmetric _ _ _ _ _ (t / 2)

theorem hodgeHeatHilbert_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    hodgeHeatHilbert g μ hμ k (s + t) =
      hodgeHeatHilbert g μ hμ k s * hodgeHeatHilbert g μ hμ k t := by
  unfold hodgeHeatHilbert
  rw [add_div]
  exact Spectral.realHeat_add _ _ _ _ _ (by positivity) (by positivity)

theorem hodgeHeatHilbert_tendsto_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    Tendsto (fun t : ℝ => hodgeHeatHilbert g μ hμ k t f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  have hscale : Tendsto (fun t : ℝ => t / 2) (𝓝[≥] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        ((continuous_id.div_const 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · change ∀ᶠ t : ℝ in 𝓝[≥] (0 : ℝ), 0 ≤ t / 2
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_nonneg ht (by norm_num)
  exact (Spectral.realHeat_tendsto_zero _ _ _ _ _ f).comp hscale

/-- The exact interface for positive-time geometric regularity: a genuine
strong derivative and membership in the original complete Hodge graph. -/
theorem hodgeHeatHilbert_strongPath (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    ∀ t, 0 < t → ∃ w : L2FormHilbert g μ k,
      HasDerivAt (fun s => hodgeHeatHilbert g μ hμ k s f) w t ∧
      (hodgeHeatHilbert g μ hμ k t f, (-2 : ℝ) • w) ∈
        (hodgeCoreOperator g μ hμ k).closure.graph := by
  intro t ht
  let w : L2FormHilbert g μ k := (1 / 2 : ℝ) •
    (hodgeHeatHilbert g μ hμ k t f - hodgeHeatHilbertInverse g μ hμ k t f)
  refine ⟨w, ?_, ?_⟩
  · have hd := Spectral.realHeat_apply_hasDerivAt (hodgeResolventOne g μ hμ k)
      (hodgeResolventOne_symmetric g μ hμ k) (hodgeResolventOne_positive g μ hμ k)
      (hodgeResolventOne_bound g μ hμ k) (hodgeResolventOne_injective g μ hμ k)
      (by positivity : 0 < t / 2) f
    have hh := hd.scomp t ((hasDerivAt_id t).div_const 2)
    simpa only [Function.comp_def, id_eq, hodgeHeatHilbert, hodgeHeatHilbertInverse, w,
      one_div] using hh
  · have hg := hodgeResolventOne_graph g μ hμ k (hodgeHeatHilbertInverse g μ hμ k t f)
    have he : hodgeResolventOne g μ hμ k (hodgeHeatHilbertInverse g μ hμ k t f) =
        hodgeHeatHilbert g μ hμ k t f := by
      rw [hodgeHeatHilbert_factor g μ hμ k ht]
      rfl
    rw [he] at hg
    have hw : (-2 : ℝ) • w =
        hodgeHeatHilbertInverse g μ hμ k t f - hodgeHeatHilbert g μ hμ k t f := by
      dsimp only [w]
      module
    rw [hw]
    exact hg

end Yau.NodeProofs.P06Aux
