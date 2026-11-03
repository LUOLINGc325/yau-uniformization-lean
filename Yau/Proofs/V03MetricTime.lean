import Yau.Proofs.V03MetricSmooth
import Yau.Proofs.V03DualTransport

/-! Smoothness of the actual inverse norm for a jointly smooth metric
family, retaining its one-sided time domain. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_entry_realMetricFn (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (i j : Fin n) :
    hMat h x z i j = ((realMetricFn h x z (i, 0) (j, 0) / 2 : ℝ) : ℂ) +
      Complex.I * ((realMetricFn h x z (i, 1) (j, 0) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [realMetricFn, realVec, hMat, stdVec, chartVec_smul,
      HermitianInnerProduct.map_smul_left, HermitianInnerProduct.map_smul_right] <;> ring

theorem metricFamily_hMat_contDiffOn {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => hMat (h p.2) x p.1 i j)
      (chartTarget x ×ˢ I) := by
  have h00 := hh x (i, 0) (j, 0)
  have h10 := hh x (i, 1) (j, 0)
  have hs := (Complex.ofRealCLM.contDiff.comp_contDiffOn (h00.div_const 2)).add
    ((contDiffOn_const (c := Complex.I)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (h10.div_const 2)))
  apply hs.congr
  intro p _
  exact hMat_entry_realMetricFn (h p.2) x p.1 i j

theorem metricFamily_hMat_inverse_contDiffOn {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (hMat (h p.2) x p.1)⁻¹ i j)
      (chartTarget x ×ˢ I) :=
  entrywise_matrix_inv_contDiffOn (metricFamily_hMat_contDiffOn hh x)
    (fun p hp => ne_of_gt (hMat_posDef (h p.2) x p.1 hp.1).det_pos) i j

theorem metricFamily_dualNormChart_contDiffOn {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => dualNormChart (h p.2) x p.1.1 p.1.2)
      (cotangentTarget x ×ˢ I) := by
  have hξ (i : Fin n) : ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ => p.1.2 i)
      (cotangentTarget x ×ˢ I) :=
    ((contDiff_piLp_apply (p := 2) (i := i)).comp (contDiff_snd.comp contDiff_fst)).contDiffOn
  have hp : ContDiff ℝ ∞ (fun p : CotangentCoord n × ℝ => (p.1.1, p.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have hi (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : CotangentCoord n × ℝ => (hMat (h p.2) x p.1.1)⁻¹ i j)
      (cotangentTarget x ×ˢ I) :=
    (metricFamily_hMat_inverse_contDiffOn hh x i j).comp hp.contDiffOn
      (fun p hp => ⟨hp.1.1, hp.2⟩)
  have hC : ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      ∑ i, star (p.1.2 i) * ∑ j, (hMat (h p.2) x p.1.1)⁻¹ j i * p.1.2 j)
      (cotangentTarget x ×ˢ I) :=
    ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hξ i)).mul
      (ContDiffOn.sum fun j _ => (hi j i).mul (hξ j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

end Yau.Blueprint.V03Proof
