import Yau.Proofs.P06HilbertTimeSmooth
import Yau.Proofs.P06StrongUniqueness

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine strong solution of the original closed graph is, after any
positive starting time, the already constructed canonical heat path. -/
theorem hodgeStrongPath_translate (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t, (-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    {a : ℝ} (ha : 0 < a) :
    ∀ t, 0 < t → h (a + t) = hodgeHeatHilbert g μ hμ k t (h a) := by
  have hshift : ∀ t, 0 < t → ∃ w, HasDerivAt (fun s => h (a + s)) w t ∧
      (h (a + t), (-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph := by
    intro t ht
    obtain ⟨w, hd, hg⟩ := hheat (a + t) (add_pos ha ht)
    refine ⟨w, ?_, hg⟩
    simpa only [Function.comp_def, one_smul] using
      hd.scomp t ((hasDerivAt_id t).const_add a)
  obtain ⟨w, hd, _⟩ := hheat a ha
  have htend : Tendsto (fun s : ℝ => a + s) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hc : Continuous (fun s : ℝ => a + s) := continuous_const.add continuous_id
    simpa only [add_zero] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hinit : Tendsto (fun s => h (a + s)) (𝓝[>] (0 : ℝ)) (𝓝 (h a)) :=
    hd.continuousAt.tendsto.comp htend
  exact hodgeStrongPath_eq_heat g μ hμ k (h a) (fun s => h (a + s)) hshift hinit

/-- The strong-path input to geometric regularity already has genuine
Hilbert C∞ time regularity, without an initial-value assumption at zero. -/
theorem hodgeStrongPath_contDiffOn (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t, (-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    ContDiffOn ℝ ∞ h (Set.Ioi 0) := by
  apply isOpen_Ioi.contDiffOn_iff.mpr
  intro t ht
  change 0 < t at ht
  have hhalf : 0 < t / 2 := by positivity
  have hAt := (hodgeHeatHilbert_contDiffOn g μ hμ k (h (t / 2))).contDiffAt
    (Ioi_mem_nhds hhalf)
  have he : t - t / 2 = t / 2 := by ring
  have hAt' : ContDiffAt ℝ ∞
      (fun s => hodgeHeatHilbert g μ hμ k s (h (t / 2))) (t - t / 2) := by
    rw [he]
    exact hAt
  have hcomp : ContDiffAt ℝ ∞
      (fun s => hodgeHeatHilbert g μ hμ k (s - t / 2) (h (t / 2))) t :=
    hAt'.comp t (contDiffAt_id.sub contDiffAt_const)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with s hs
  change t / 2 < s at hs
  have hout := hodgeStrongPath_translate g μ hμ k h hheat hhalf (s - t / 2) (by linarith)
  simpa only [add_sub_cancel] using hout

theorem hodgeStrongPath_bounded_graph_chain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t, (-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ u : ℕ → L2FormHilbert g μ k, u 0 = h t ∧
      (∀ j, j < m → (u j, u (j + 1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) ∧
      ∀ j, j ≤ m → ‖u j‖ ≤ (4 * (m : ℝ) / t) ^ j * ‖h (t / 2)‖ := by
  have hhalf : 0 < t / 2 := by positivity
  obtain ⟨u, hu, hchain, hbound⟩ :=
    hodgeHeatHilbert_bounded_graph_chain g μ hμ k (h (t / 2)) hhalf m
  have he := hodgeStrongPath_translate g μ hμ k h hheat hhalf (t / 2) hhalf
  rw [add_halves] at he
  have hcoef : 2 * (m : ℝ) / (t / 2) = 4 * (m : ℝ) / t := by ring
  exact ⟨u, hu.trans he.symm, hchain, by simpa only [hcoef] using hbound⟩

end Yau.NodeProofs.P06Aux
