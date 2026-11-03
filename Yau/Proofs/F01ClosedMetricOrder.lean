import Yau.Proofs.F01FamilyRayleighSmooth
import Yau.Proofs.F01ClosedRicciFamily
import Yau.Proofs.F01ClosedHeatContinuity
import Yau.Proofs.F01LeviOrder

/-! A native Hermitian matrix inequality on the interior extends to both
faces of the original smooth time slab. This uses actual quadratic forms. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem closed_metric_upper_order_of_interior
    (α : HermitianField M) (h : ℝ → HermitianField M) {T C : ℝ}
    (hT : 0 < T) (hh : MetricFamilySmooth h (Icc 0 T))
    (horder : ∀ x t, t ∈ Ioo 0 T → ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef) :
    ∀ x t, t ∈ Icc 0 T → ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef := by
  intro x t ht
  have hα := (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x)
    (mem_extChartAt_target x)).isHermitian
  have hB : ((C : ℂ) • gMat α x).IsHermitian :=
    hα.smul (show IsSelfAdjoint (C : ℂ) from Complex.conj_ofReal C)
  have hH := (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x)
    (mem_extChartAt_target x)).isHermitian
  apply (matrix_posSemidef_sub_iff_quadratic hH hB).mpr
  intro v
  have hc : ContinuousOn (fun s => matrixQuadraticValue (gMat (h s) x) v -
      matrixQuadraticValue ((C : ℂ) • gMat α x) v) (Icc 0 T) :=
    (matrixQuadraticValue_contDiffOn (fun s => gMat (h s) x) v (Icc 0 T)
      (fun i j => metricFamily_gMat_time_smooth h hh x i j)).continuousOn.sub
        continuousOn_const
  have hineq : ∀ s ∈ Ioo 0 T, matrixQuadraticValue (gMat (h s) x) v -
      matrixQuadraticValue ((C : ℂ) • gMat α x) v ≤ 0 := by
    intro s hs
    have hHs := (Yau.LeafProofs.L12Aux.hMat_posDef (h s) x (chartPt x x)
      (mem_extChartAt_target x)).isHermitian
    exact sub_nonpos.mpr ((matrix_posSemidef_sub_iff_quadratic hHs hB).mp
      (horder x s hs) v)
  exact sub_nonpos.mp (continuous_closed_interval_nonpos_of_interior hT hc hineq t ht)

end Yau.NodeProofs.F01Aux
