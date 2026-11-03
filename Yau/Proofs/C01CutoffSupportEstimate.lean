import Yau.Proofs.C01IndexOptimization
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A true weighted cutoff estimate and the actual pointwise Ricci
bound give exactly the square-root-time loss for the distance support. -/

noncomputable section
open MeasureTheory
open scoped Topology Interval

namespace Yau.NodeProofs.C01Aux

theorem cutoff_integral_support_estimate
    (R : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (a d B C : ℝ) (ha : 0 < a) (hd : 0 < d) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hpoint : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ R u ∧ R u ≤ C * (1 + d ^ 2) * d ^ 2 / a)
    (hindex : ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 →
      (∫ u in Set.Icc (0 : ℝ) 1, indexCutoff κ u ^ 2 * R u) ≤ B / κ) :
    (∫ u in Set.Icc (0 : ℝ) 1, R u) / (2 * d) ≤
      (B + C + 1) * (1 + d) / Real.sqrt a := by
  have hsqrt : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hi : IntegrableOn R (Set.Icc (0 : ℝ) 1) volume := hR.integrableOn_compact isCompact_Icc
  have hc : IntegrableOn (fun _u : ℝ => C * (1 + d ^ 2) * d ^ 2 / a)
      (Set.Icc (0 : ℝ) 1) volume := integrableOn_const (hs := by simp)
  have hfull : (∫ u in Set.Icc (0 : ℝ) 1, R u) ≤ C * (1 + d ^ 2) * d ^ 2 / a := by
    have H := setIntegral_mono_on hi hc measurableSet_Icc (fun u hu => (hpoint u hu).2)
    simpa [integral_const, Measure.real] using H
  apply index_integral_optimized_bound d (Real.sqrt a) B C _ hd (Real.sqrt_pos.mpr ha) hB hC
  · rwa [hsqrt]
  · intro κ hκ hκhalf
    have hweight : (∫ u in (0 : ℝ)..1, indexCutoff κ u ^ 2 * R u) ≤ B / κ := by
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
      exact hindex κ hκ hκhalf
    have H := index_integral_bound_of_weighted R hR (fun u hu => (hpoint u hu).1)
      κ (C * (1 + d ^ 2) * d ^ 2 / a) (B / κ) hκ hκhalf
      (fun u hu => (hpoint u hu).2) hweight
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at H
    exact H.trans_eq (by rw [hsqrt]; ring)

end Yau.NodeProofs.C01Aux
