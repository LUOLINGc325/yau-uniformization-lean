import Yau.Proofs.C03TargetChartsCover
import Yau.Proofs.C03TargetChartsQuadratic

/-! One finite target atlas has uniform actual metric bounds and a positive margin. -/
noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.TargetCharts
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.Proofs.P04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_finite_metric_chart_cover (g : SmoothMetric M)
    (K : Set M.Carrier) (hK : IsCompact K) :
    ∃ (I : Finset M.Carrier) (r : M.Carrier → ℝ) (d U L δ : ℝ),
      0 < d ∧ 0 < U ∧ 0 < L ∧ 0 < δ ∧
      (∀ a ∈ I, 0 < r a ∧ δ ≤ r a ∧
        Metric.closedBall (chartPt a a) (4 * r a) ⊆ chartTarget a ∧
        ∀ w ∈ Metric.closedBall (chartPt a a) (4 * r a),
          HermLE ((d : ℂ) • (1 : Herm n)) (hMat g.form a w) ∧
          HermLE (hMat g.form a w) ((U : ℂ) • (1 : Herm n)) ∧
          ∀ v : ComplexVector n, realMetricInChart g.form a w v v ≤ L ^ 2 * ‖v‖ ^ 2) ∧
      K ⊆ ⋃ a ∈ I, chartInv a '' Metric.ball (chartPt a a) (r a) := by
  classical
  obtain ⟨r, I, hr, ht, hcover⟩ := exists_finite_chart_cover K hK
  have hlocal (a : M.Carrier) := compact_chart_quadratic_bounds g a
    (Metric.closedBall (chartPt a a) (4 * r a)) (isCompact_closedBall _ _) (ht a)
  choose da Ua hda hUa hq using hlocal
  obtain ⟨d, hd, hdle⟩ := finite_positive_minorant I da (fun a _ => hda a)
  obtain ⟨δ, hδ, hδle⟩ := finite_positive_minorant I r (fun a _ => hr a)
  let U := 1 + ∑ a ∈ I, Ua a
  have hU : 0 < U := by
    have hs : 0 ≤ ∑ a ∈ I, Ua a := Finset.sum_nonneg (fun a _ => (hUa a).le)
    dsimp [U]
    linarith
  have hUle (a : M.Carrier) (ha : a ∈ I) : Ua a ≤ U := by
    have hs := Finset.single_le_sum (fun b (_ : b ∈ I) => (hUa b).le) ha
    dsimp [U]
    linarith
  let L := Real.sqrt (2 * U) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hLsq : 2 * U ≤ L ^ 2 := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * U)
    dsimp [L]
    nlinarith [Real.sqrt_nonneg (2 * U)]
  refine ⟨I, r, d, U, L, δ, hd, hU, hL, hδ, ?_, hcover⟩
  intro a ha
  refine ⟨hr a, hδle a ha, ht a, ?_⟩
  intro w hw
  have hlo (v : ComplexVector n) : d * ‖v‖ ^ 2 ≤ matrixQuadratic (hMat g.form a w) v :=
    (mul_le_mul_of_nonneg_right (hdle a ha) (sq_nonneg _)).trans (hq a w hw v).1
  have hup (v : ComplexVector n) : matrixQuadratic (hMat g.form a w) v ≤ U * ‖v‖ ^ 2 :=
    (hq a w hw v).2.trans (mul_le_mul_of_nonneg_right (hUle a ha) (sq_nonneg _))
  refine ⟨matrix_lower_of_quadratic _ (hMat_isHermitian g.form a w) d hlo,
    matrix_upper_of_quadratic _ (hMat_isHermitian g.form a w) U hup, ?_⟩
  intro v
  exact (realMetric_le_of_quadratic g a w (ht a hw) U hup v).trans
    (mul_le_mul_of_nonneg_right hLsq (sq_nonneg _))

end Yau.Proofs.C03Aux.TargetCharts
