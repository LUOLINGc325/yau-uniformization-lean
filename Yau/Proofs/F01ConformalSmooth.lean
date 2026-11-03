import Yau.Proofs.F01ConformalMetric
import Yau.Proofs.F01ConformalProfile

/-! Actual chartwise smoothness of exp(f)g, kept as a Hermitian field. -/
open Set
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem conformalField_realMetricFn (h : HermitianField M) (f : M.Carrier → ℝ)
    (a : M.Carrier) (z : ComplexVector n) (i j : RIdx n) :
    realMetricFn (conformalField h f) a z i j =
      Real.exp (f (chartInv a z)) * realMetricFn h a z i j := by
  simp only [realMetricFn, conformalField_value, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem conformalField_metricSmooth {h : HermitianField M} {f : M.Carrier → ℝ}
    (hh : MetricSmooth h) (hf : SmoothFn f) : MetricSmooth (conformalField h f) := by
  intro a i j
  simpa only [conformalField_realMetricFn, inChart] using (hf a).exp.mul (hh a i j)

theorem conformalScalar_contDiffOn {u : M.Carrier → ℝ} (hu : SmoothFn u)
    {L : ℝ} (hL : 0 < L) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (inChart a (conformalScalar u L))
      (chartTarget a ∩ {z | u (chartInv a z) < L}) := by
  have hinner : ContDiffOn ℝ ∞ (fun z => u (chartInv a z) / L)
      (chartTarget a ∩ {z | u (chartInv a z) < L}) :=
    ((hu a).div_const L).mono inter_subset_left
  exact conformalProfile_contDiffOn.comp hinner (by
    intro z hz
    exact (div_lt_one hL).mpr hz.2)

end Yau.NodeProofs.F01Aux
