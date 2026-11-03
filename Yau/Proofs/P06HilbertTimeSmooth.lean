import Yau.Proofs.P06HodgeSpectralBounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem hodgeHeatHilbert_hasDerivAt_of_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) {x y : L2FormHilbert g μ k}
    (hxy : (x, y) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => hodgeHeatHilbert g μ hμ k s x)
      ((-1 / 2 : ℝ) • hodgeHeatHilbert g μ hμ k t y) t := by
  obtain ⟨w, hd, hg⟩ := hodgeHeatHilbert_strongPath g μ hμ k x t ht
  have he := (hodgeCoreOperator g μ hμ k).closure.mem_graph_snd_inj hg
    (hodgeHeatHilbert_graph g μ hμ k t hxy) rfl
  have hw : w = (-1 / 2 : ℝ) • hodgeHeatHilbert g μ hμ k t y := by
    have h := congrArg (fun v : L2FormHilbert g μ k => (-1 / 2 : ℝ) • v) he
    simpa only [smul_smul, show (-1 / 2 : ℝ) * (-2) = 1 by norm_num, one_smul] using h
  rwa [hw] at hd

theorem hodgeHeatHilbert_continuousOn (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    ContinuousOn (fun t => hodgeHeatHilbert g μ hμ k t f) (Set.Ioi 0) := by
  intro t ht
  obtain ⟨w, hd, _⟩ := hodgeHeatHilbert_strongPath g μ hμ k f t ht
  exact hd.continuousAt.continuousWithinAt

theorem hodgeHeatHilbert_contDiffOn_of_chain (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (m : ℕ)
    (a : ℕ → L2FormHilbert g μ k)
    (hchain : ∀ j, j < m → (a j, a (j + 1)) ∈ (hodgeCoreOperator g μ hμ k).closure.graph) :
    ContDiffOn ℝ m (fun t => hodgeHeatHilbert g μ hμ k t (a 0)) (Set.Ioi 0) := by
  induction m generalizing a with
  | zero => exact contDiffOn_zero.mpr (hodgeHeatHilbert_continuousOn g μ hμ k (a 0))
  | succ m ih =>
    have ht := ih (fun j => a (j + 1)) (fun j hj => hchain (j + 1) (by omega))
    have hD : ContDiffOn ℝ m
        (fun t => (-1 / 2 : ℝ) • hodgeHeatHilbert g μ hμ k t (a 1)) (Set.Ioi 0) :=
      ht.const_smul (-1 / 2 : ℝ)
    have hs : ContDiffOn ℝ ((m : ℕ∞ω) + 1)
        (fun t => hodgeHeatHilbert g μ hμ k t (a 0)) (Set.Ioi 0) := by
      apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mpr
      refine ⟨?_, by simp, ?_⟩
      · intro t ht
        exact (hodgeHeatHilbert_hasDerivAt_of_graph g μ hμ k (hchain 0 (by omega)) ht).differentiableAt.differentiableWithinAt
      · apply hD.congr
        intro t ht
        exact (hodgeHeatHilbert_hasDerivAt_of_graph g μ hμ k (hchain 0 (by omega)) ht).deriv
    simpa only [Nat.cast_add, Nat.cast_one] using hs

/-- Every positive-time Hilbert path is C∞ in time. Together with the
proved arbitrary graph-chain bounds this permits elliptic regularity of
the actual geometric Hodge operator, without presupposing a smooth path. -/
theorem hodgeHeatHilbert_contDiffOn (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (f : L2FormHilbert g μ k) :
    ContDiffOn ℝ ∞ (fun t => hodgeHeatHilbert g μ hμ k t f) (Set.Ioi 0) := by
  apply contDiffOn_infty.mpr
  intro m
  apply isOpen_Ioi.contDiffOn_iff.mpr
  intro t ht
  change 0 < t at ht
  have hhalf : 0 < t / 2 := by positivity
  obtain ⟨a, ha, hchain⟩ := hodgeHeatHilbert_graph_chain g μ hμ k f hhalf m
  have hAt := (hodgeHeatHilbert_contDiffOn_of_chain g μ hμ k m a hchain).contDiffAt
    (Ioi_mem_nhds hhalf)
  have he : t - t / 2 = t / 2 := by ring
  rw [← he] at hAt
  have hcomp : ContDiffAt ℝ m
      (fun s => hodgeHeatHilbert g μ hμ k (s - t / 2) (a 0)) t :=
    hAt.comp t (contDiffAt_id.sub contDiffAt_const)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with s hs
  change t / 2 < s at hs
  rw [ha]
  change hodgeHeatHilbert g μ hμ k s f =
    (hodgeHeatHilbert g μ hμ k (s - t / 2) * hodgeHeatHilbert g μ hμ k (t / 2)) f
  rw [← hodgeHeatHilbert_add g μ hμ k (by linarith : 0 ≤ s - t / 2) hhalf.le,
    sub_add_cancel]

end Yau.NodeProofs.P06Aux
