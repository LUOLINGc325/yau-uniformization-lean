import Yau.LeafProofs.L17ChartNaturality

/-! Joint metric smoothness controls the actual complex Hermitian entries,
including the closed time faces in the original time set. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_hMat_contDiffOn (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (a : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => hMat (h p.2) a p.1 i j)
      (chartTarget a ×ˢ I) := by
  have hr := (contDiffOn_const.mul (hh a (i, 0) (j, 0)) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      (1 / 2 : ℝ) * realMetricFn (h p.2) a p.1 (i, 0) (j, 0)) _)
  have hi := (contDiffOn_const.mul (hh a (i, 1) (j, 0)) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      (1 / 2 : ℝ) * realMetricFn (h p.2) a p.1 (i, 1) (j, 0)) _)
  have hc := (Complex.ofRealCLM.contDiff.comp_contDiffOn hr).add
    ((contDiffOn_const (c := Complex.I)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hi))
  apply hc.congr
  intro p hp
  apply Complex.ext <;>
    simp [Yau.LeafProofs.L12Aux.realMetricFn_entries, Complex.mul_re, Complex.mul_im]

end Yau.NodeProofs.F01Aux
