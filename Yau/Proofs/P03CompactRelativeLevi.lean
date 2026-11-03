import Yau.Proofs.P03RelativeLeviCoercivity
import Yau.Proofs.P03RelativeLeviTransport
import Yau.Proofs.P03StrictPshCharts
import Yau.Proofs.P03CompactPositiveBounds
import Yau.LeafProofs.L23FieldMetricNormalRadius

open scoped Manifold Topology ContDiff
open Filter Set Metric

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L22Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_local_relative_levi_lower (g : Yau.SmoothMetric M)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ) (p : M.Carrier) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ U : Set M.Carrier, U ∈ 𝓝 p ∧ ∀ x ∈ U, ∀ v,
      lam * realMetricInChart g.form x (chartPt x x) v v ≤
        complexLeviQuadratic (inChart x ψ) (chartPt x x) v := by
  obtain ⟨R, hR, hRt⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds
      (mem_extChartAt_target (I := ComplexModel n) p))
  let r := R / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hKtarget : closedBall (chartPt p p) r ⊆ chartTarget p :=
    (Metric.closedBall_subset_ball (by dsimp only [r]; linarith)).trans hRt
  obtain ⟨lam, hlam, hbound⟩ := exists_compact_relative_levi_lower g p (hψ.1 p)
    (isCompact_closedBall (chartPt p p) r) hKtarget
    (fun z hz => strictPsh_chart_posDef hψ p (hKtarget hz))
  let U : Set M.Carrier := (extChartAt (ComplexModel n) p).source ∩
    chartPt p ⁻¹' ball (chartPt p p) r
  have hU : IsOpen U := by
    exact isOpen_extChartAt_preimage' (I := ComplexModel n) p isOpen_ball
  have hp : p ∈ U := ⟨mem_extChartAt_source p, mem_ball_self hr⟩
  refine ⟨lam, hlam, U, hU.mem_nhds hp, ?_⟩
  intro x hx v
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hsource : chartInv x (chartPt x x) ∈ (extChartAt (ComplexModel n) p).source := by
    simpa only [hi] using hx.1
  apply inChart_relativeLevi_transport g.form hψ.1 x p (mem_extChartAt_target x) hsource lam _ v
  intro w
  change lam * realMetricInChart g.form p (chartPt p (chartInv x (chartPt x x))) w w ≤
    complexLeviQuadratic (inChart p ψ) (chartPt p (chartInv x (chartPt x x))) w
  rw [hi]
  exact hbound (chartPt p x) (ball_subset_closedBall hx.2) w

/-- A compact set in the actual manifold has one positive relative Levi
constant, chosen before any regularized pole weight. -/
theorem exists_compact_manifold_relative_levi_lower (g : Yau.SmoothMetric M)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ v,
      lam * realMetricInChart g.form x (chartPt x x) v v ≤
        complexLeviQuadratic (inChart x ψ) (chartPt x x) v := by
  apply exists_compact_positive_bound
    (fun t x => ∀ v, t * realMetricInChart g.form x (chartPt x x) v v ≤
      complexLeviQuadratic (inChart x ψ) (chartPt x x) v) _ _ hK
  · intro s t hst x hx v
    exact (mul_le_mul_of_nonneg_right hst
      (realMetricInChart_quadratic_nonneg g.form x (chartPt x x) v)).trans (hx v)
  · intro x
    exact exists_local_relative_levi_lower g ψ hψ x

end Yau.NodeProofs.P03Aux
