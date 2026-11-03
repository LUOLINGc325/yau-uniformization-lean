import Yau.Proofs.F01ClosedMetricOrder

/-! The actual lower metric order extends to both closed time faces
by continuity of its native Hermitian quadratic forms. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem closed_metric_lower_order_of_interior
    (α : HermitianField M) (h : ℝ → HermitianField M) {T c : ℝ}
    (hT : 0 < T) (hh : MetricFamilySmooth h (Icc 0 T))
    (horder : ∀ x t, t ∈ Ioo 0 T → (gMat (h t) x - (c : ℂ) • gMat α x).PosSemidef) :
    ∀ x t, t ∈ Icc 0 T → (gMat (h t) x - (c : ℂ) • gMat α x).PosSemidef := by
  intro x t ht
  have hα := (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x)
    (mem_extChartAt_target x)).isHermitian
  have hA : ((c : ℂ) • gMat α x).IsHermitian :=
    hα.smul (show IsSelfAdjoint (c : ℂ) from Complex.conj_ofReal c)
  have hH := (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x)
    (mem_extChartAt_target x)).isHermitian
  apply (matrix_posSemidef_sub_iff_quadratic hA hH).mpr
  intro v
  have hc : ContinuousOn (fun s => matrixQuadraticValue ((c : ℂ) • gMat α x) v -
      matrixQuadraticValue (gMat (h s) x) v) (Icc 0 T) :=
    continuousOn_const.sub (matrixQuadraticValue_contDiffOn (fun s => gMat (h s) x) v (Icc 0 T)
      (fun i j => metricFamily_gMat_time_smooth h hh x i j)).continuousOn
  have hineq : ∀ s ∈ Ioo 0 T, matrixQuadraticValue ((c : ℂ) • gMat α x) v -
      matrixQuadraticValue (gMat (h s) x) v ≤ 0 := by
    intro s hs
    have hHs := (Yau.LeafProofs.L12Aux.hMat_posDef (h s) x (chartPt x x)
      (mem_extChartAt_target x)).isHermitian
    exact sub_nonpos.mpr ((matrix_posSemidef_sub_iff_quadratic hA hHs).mp (horder x s hs) v)
  exact sub_nonpos.mp (continuous_closed_interval_nonpos_of_interior hT hc hineq t ht)

end Yau.NodeProofs.F01Aux
