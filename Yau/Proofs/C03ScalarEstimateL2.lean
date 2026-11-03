import Yau.Geometry.Basic
import Mathlib

/-! The same weighted correction controls the actual unweighted norm on a fixed source ball. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Topology ENNReal
namespace Yau.Proofs.C03Aux.ScalarEstimate
open Yau
variable {n : ℕ}

theorem correction_L2_le (f h : ComplexVector n → ℂ) (φ : ComplexVector n → ℝ)
    (R M B : ℝ) (hf : Continuous f) (hh : Continuous h) (hφ : Continuous φ)
    (hB : 0 ≤ B) (hφM : ∀ z ∈ closedBall (0 : ComplexVector n) R, φ z ≤ M)
    (hb : (∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-φ z))
      ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal B) :
    (∫ z in closedBall (0 : ComplexVector n) R, ‖f z - h z‖ ^ 2) ≤ Real.exp M * B := by
  have hc : Continuous (fun z => ‖f z - h z‖ ^ 2) := (hf.sub hh).norm.pow 2
  have hw : Continuous (fun z => ‖f z - h z‖ ^ 2 * Real.exp (-φ z)) :=
    hc.mul (Real.continuous_exp.comp hφ.neg)
  have hi := hc.continuousOn.integrableOn_compact (μ := (volume : Measure (ComplexVector n))) (isCompact_closedBall (0 : ComplexVector n) R)
  have hwi := hw.continuousOn.integrableOn_compact (μ := (volume : Measure (ComplexVector n))) (isCompact_closedBall (0 : ComplexVector n) R)
  have hwB : (∫ z in closedBall (0 : ComplexVector n) R,
      ‖f z - h z‖ ^ 2 * Real.exp (-φ z)) ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hB).mp
    rw [ofReal_integral_eq_lintegral_ofReal hwi
      (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))]
    exact (setLIntegral_le_lintegral _ _).trans hb
  calc
    _ ≤ ∫ z in closedBall (0 : ComplexVector n) R,
        Real.exp M * (‖f z - h z‖ ^ 2 * Real.exp (-φ z)) := by
      apply setIntegral_mono_on hi (hwi.const_mul _) measurableSet_closedBall
      intro z hz
      have he : 1 ≤ Real.exp M * Real.exp (-φ z) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [hφM z hz])
      calc
        _ ≤ (Real.exp M * Real.exp (-φ z)) * ‖f z - h z‖ ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) he
        _ = _ := by ring
    _ = Real.exp M * ∫ z in closedBall (0 : ComplexVector n) R,
        ‖f z - h z‖ ^ 2 * Real.exp (-φ z) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hwB (Real.exp_pos _).le

theorem local_L2_le (f h : ComplexVector n → ℂ) (φ : ComplexVector n → ℝ)
    (R M S B : ℝ) (hf : Continuous f) (hh : Continuous h) (hφ : Continuous φ)
    (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hfS : ∀ z ∈ closedBall (0 : ComplexVector n) R, ‖f z‖ ≤ S)
    (hφM : ∀ z ∈ closedBall (0 : ComplexVector n) R, φ z ≤ M)
    (hb : (∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-φ z))
      ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal B) :
    (∫ z in closedBall (0 : ComplexVector n) R, ‖h z‖ ^ 2) ≤
      2 * S ^ 2 * (volume : Measure (ComplexVector n)).real (closedBall 0 R) +
        2 * Real.exp M * B := by
  have he := correction_L2_le f h φ R M B hf hh hφ hB hφM hb
  have hhi := (hh.norm.pow 2).continuousOn.integrableOn_compact (μ := (volume : Measure (ComplexVector n)))
    (isCompact_closedBall (0 : ComplexVector n) R)
  have hei := ((hf.sub hh).norm.pow 2).continuousOn.integrableOn_compact (μ := (volume : Measure (ComplexVector n)))
    (isCompact_closedBall (0 : ComplexVector n) R)
  have hci : IntegrableOn (fun _ : ComplexVector n => 2 * S ^ 2)
      (closedBall 0 R) volume := continuous_const.continuousOn.integrableOn_compact (μ := (volume : Measure (ComplexVector n)))
        (isCompact_closedBall (0 : ComplexVector n) R)
  have hei2 : IntegrableOn (fun z => 2 * ‖f z - h z‖ ^ 2)
      (closedBall (0 : ComplexVector n) R) volume := hei.const_mul 2
  have hpoint (z : ComplexVector n) (hz : z ∈ closedBall 0 R) :
      ‖h z‖ ^ 2 ≤ 2 * S ^ 2 + 2 * ‖f z - h z‖ ^ 2 := by
    have ht : ‖h z‖ ≤ ‖f z‖ + ‖f z - h z‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le (f z) (f z - h z)
    have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have hs2 := pow_le_pow_left₀ (norm_nonneg _) (hfS z hz) 2
    nlinarith [sq_nonneg (‖f z‖ - ‖f z - h z‖)]
  calc
    _ ≤ ∫ z in closedBall (0 : ComplexVector n) R,
        (2 * S ^ 2 + 2 * ‖f z - h z‖ ^ 2) :=
      setIntegral_mono_on hhi (hci.add hei2) measurableSet_closedBall hpoint
    _ = 2 * S ^ 2 * (volume : Measure (ComplexVector n)).real (closedBall 0 R) +
        2 * ∫ z in closedBall (0 : ComplexVector n) R, ‖f z - h z‖ ^ 2 := by
      rw [integral_add hci hei2]
      simp only [integral_const_mul, setIntegral_const, smul_eq_mul]
      ring
    _ ≤ _ := by linarith

end Yau.Proofs.C03Aux.ScalarEstimate
