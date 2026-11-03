import Yau.Proofs.P03MetricTransitionMatrices
import Yau.LeafProofs.L14Gauge

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n : ℕ} {M : ComplexManifold n}

def tangentChartOverlap (a b : M.Carrier) : Set (ComplexVector n) :=
  chartTarget b ∩ (chartInv b) ⁻¹' (extChartAt (ComplexModel n) a).source

theorem tangentChartOverlap_isOpen (a b : M.Carrier) : IsOpen (tangentChartOverlap a b) :=
  (continuousOn_extChartAt_symm (I := ComplexModel n) b).isOpen_inter_preimage
    (isOpen_extChartAt_target b) (isOpen_extChartAt_source a)

theorem tangentTransition_entry_contDiffAt_chart (a c b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget b)
    (ha : chartInv b z ∈ (extChartAt (ComplexModel n) a).source)
    (hc : chartInv b z ∈ (extChartAt (ComplexModel n) c).source) (i j : Fin n) :
    ContDiffAt ℂ ∞ (fun w => determinantTransitionMatrix a c (chartInv b w) i j) z := by
  have hentry := (determinantTransitionMatrix_entry_contMDiffOn a c i j (chartInv b z)
    ⟨ha, hc⟩).contMDiffAt
      (((isOpen_extChartAt_source a).inter (isOpen_extChartAt_source c)).mem_nhds ⟨ha, hc⟩)
  have hci : ContMDiffAt (ComplexModel n) (ComplexModel n) ∞ (chartInv b) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) b).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hz)
  exact ((hentry.of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top)).comp z hci).contDiffAt

/-- The accepted holomorphic-gauge curvature theorem is applied to the
actual inverse-chart Jacobians and the actual Hermitian Gram matrices. -/
theorem tangent_curvature_overlap (g : Yau.SmoothMetric M) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ tangentChartOverlap a b) (i j : Fin n) :
    curvatureMatrix (hMat g.form b) z i j =
      (determinantTransitionMatrix b a (chartInv b z))ᴴ *
        (∑ p, ∑ q,
          (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec i) p *
            star (fderiv ℂ (fun w => chartPt a (chartInv b w)) z (stdVec j) q)) •
              curvatureMatrix (hMat g.form a) (chartPt a (chartInv b z)) p q) *
                determinantTransitionMatrix b a (chartInv b z) := by
  let O := tangentChartOverlap a b
  let T := fun w => chartPt a (chartInv b w)
  let A := fun w => determinantTransitionMatrix b a (chartInv b w)
  let C := fun w => determinantTransitionMatrix a b (chartInv b w)
  have hO := tangentChartOverlap_isOpen a b
  have hTU : Set.MapsTo T O (chartTarget a) :=
    fun w hw => (extChartAt (ComplexModel n) a).map_source hw.2
  have hT : ContDiffOn ℂ ∞ T O := by
    intro w hw
    exact (L18Aux.chartTransition_contDiffAt b a hw.1 hw.2).contDiffWithinAt
  have hA (α β : Fin n) : ContDiffOn ℂ ∞ (fun w => A w α β) O := by
    intro w hw
    exact (tangentTransition_entry_contDiffAt_chart b a b hw.1
      ((extChartAt (ComplexModel n) b).map_target hw.1) hw.2 α β).contDiffWithinAt
  have hC (α β : Fin n) : ContDiffOn ℂ ∞ (fun w => C w α β) O := by
    intro w hw
    exact (tangentTransition_entry_contDiffAt_chart a b b hw.1 hw.2
      ((extChartAt (ComplexModel n) b).map_target hw.1) α β).contDiffWithinAt
  have hAC (w : ComplexVector n) (hw : w ∈ O) : A w * C w = 1 :=
    determinantTransitionMatrix_mul_reverse b a (chartInv b w)
      ((extChartAt (ComplexModel n) b).map_target hw.1) hw.2
  have hEq : Set.EqOn (hMat g.form b)
      (fun w => (A w)ᴴ * hMat g.form a (T w) * A w) O := by
    intro w hw
    have hi : chartPt b (chartInv b w) = w := (extChartAt (ComplexModel n) b).right_inv hw.1
    have he := hMat_chart_change g.form b a (chartInv b w)
      ((extChartAt (ComplexModel n) b).map_target hw.1) hw.2
    rw [hi] at he
    exact he
  have hcong := congrArg (fun R => R i j)
    (L14Aux.curvatureMatrix_congr_of_eqOn _ _ hO hEq z hz)
  exact hcong.trans (L14Aux.curvatureMatrix_holomorphic_change hO
    (isOpen_extChartAt_target a) (hMat g.form a) T A C
    (L18Aux.hMat_contDiffOn g a)
    (fun w hw => ne_of_gt (hMat_posDef g.form a w hw).det_pos)
    hT hTU hA hC hAC z hz i j)

end Yau.NodeProofs.P03Aux
