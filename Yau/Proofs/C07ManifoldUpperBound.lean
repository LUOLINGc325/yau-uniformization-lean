import Yau.Proofs.D04Comparison
import Yau.Proofs.D04AtlasGlueCover
import Yau.Proofs.D04AtlasGlueVolumeCompare

open MeasureTheory Set
open scoped Topology Manifold

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- A manifold psh representative inherits a finite upper bound holding
almost everywhere on every compact, with respect to the same genuine
Riemannian volume. -/
theorem manifold_psh_le_of_ae_compact_bound
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) {u : M.Carrier → EReal} (hu : IsPsh u) {C : ℝ}
    (hbound : ∀ K : Set M.Carrier, IsCompact K → ∀ᵐ x ∂μ.restrict K, u x ≤ (C : EReal)) :
    ∀ x, u x ≤ (C : EReal) := by
  have hcenter (B : Yau.Proofs.D04AtlasGlueAux.ChartBall M) : u B.center ≤ (C : EReal) := by
    let K := Metric.closedBall (chartPt B.center B.center) B.radius
    let O := Metric.ball (chartPt B.center B.center) B.radius
    have hK : IsCompact K := isCompact_closedBall _ _
    have hKt : K ⊆ chartTarget B.center := B.closed_inner_subset_target
    have hiK : IsCompact (chartInv B.center '' K) := hK.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := ComplexModel n) B.center).mono hKt)
    have hae := Yau.Proofs.D04AtlasGlueAux.ae_chart_compact_pullback
      g hg μ hμ B.center hK hKt (hbound _ hiK)
    rw [Yau.LeafProofs.lebesgueC_eq_volume] at hae
    have hOt : O ⊆ chartTarget B.center := Metric.ball_subset_closedBall.trans hKt
    have hcoord := (Yau.Proofs.D04Aux.pshOnManifold_univ_of_isPsh hu).2.2 B.center
    have hcoord' : IsPshOn (fun z => u (chartInv B.center z)) (chartTarget B.center) := by
      simpa only [Set.mem_univ, and_true, Set.setOf_mem_eq] using hcoord
    have hpsh := Yau.Proofs.D04Aux.isPshOn_mono hcoord' hOt
    have hupper := Yau.Proofs.D04Aux.psh_le_usc_of_ae_le Metric.isOpen_ball hpsh
      upperSemicontinuousOn_const
      (ae_restrict_of_ae_restrict_of_subset Metric.ball_subset_closedBall hae)
      (chartPt B.center B.center) (Metric.mem_ball_self B.radius_pos)
    simpa only [chartInv, chartPt,
      (extChartAt (ComplexModel n) B.center).left_inv (mem_extChartAt_source B.center)] using hupper
  intro x
  obtain ⟨B, hB⟩ := Yau.Proofs.D04AtlasGlueAux.exists_chartBall x
  simpa only [hB] using hcenter B

end Yau.Proofs.C07Aux
