import Yau.Proofs.C04ClockInverse
import Yau.Proofs.C04MiddlePoint

/-! The source's middle-half logarithmic derivative estimate in physical time. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem middle_point_of_good_window (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ S K : ℝ, B ≤ S → 1 ≤ K →
      (∀ t t', 0 ≤ t → 0 ≤ t' → ρ o t = 2 * S → ρ o t' = a * S →
        clockSpeed o h t ≤ K * clockSpeed o h t') →
      ∃ tw : ℝ, 0 < tw ∧ 5 * S / 4 ≤ ρ o tw ∧ ρ o tw ≤ 7 * S / 4 ∧
        0 ≤ deriv (clockSpeed o h) tw /
          (clockSpeed o h tw * scalarCurvature (h tw) o) ∧
        deriv (clockSpeed o h) tw /
          (clockSpeed o h tw * scalarCurvature (h tw) o) ≤ 2 * Real.log K / S := by
  obtain ⟨A, hA, hsA, time, htime, hleft, hstrict, htinf⟩ :=
    clock_inverse X o h U P ρ hf hH
  let B := max 1 (ρ o A / a)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro S K hBS hK hwindow
  have hS : 0 < S := hB.trans_le hBS
  have hbase : ρ o A ≤ a * S := by
    have hh := (le_max_right 1 (ρ o A / a)).trans hBS
    simpa only [mul_comm S a] using (div_le_iff₀ ha).mp hh
  have hsmall : a * S ≤ 5 * S / 4 := by nlinarith
  have hmiddle : 5 * S / 4 < 7 * S / 4 := by linarith
  have hlarge : 7 * S / 4 ≤ 2 * S := by linarith
  have hbaseL : ρ o A ≤ 5 * S / 4 := hbase.trans hsmall
  have hbaseR : ρ o A ≤ 7 * S / 4 := hbaseL.trans hmiddle.le
  have hbase2 : ρ o A ≤ 2 * S := hbaseR.trans hlarge
  let tl := time (5 * S / 4)
  let tr := time (7 * S / 4)
  have hAl : A ≤ tl := (htime _ hbaseL).1
  have hAr : A ≤ tr := (htime _ hbaseR).1
  have htl : 0 < tl := zero_lt_one.trans_le (hA.trans hAl)
  have htr : 0 < tr := zero_lt_one.trans_le (hA.trans hAr)
  have hlr : tl < tr := hstrict hbaseL hbaseR hmiddle
  have hsl : ρ o tl = 5 * S / 4 := (htime _ hbaseL).2
  have hsr : ρ o tr = 7 * S / 4 := (htime _ hbaseR).2
  have hm : MonotoneOn (clockSpeed o h) (Set.Ici A) :=
    clockSpeed_monotoneOn X o h U P ρ hf hH (zero_lt_one.trans_le hA)
  have hqwindow : clockSpeed o h tr ≤ K * clockSpeed o h tl := by
    have hqhi := hm hAr (htime _ hbase2).1
      (hstrict.monotoneOn hbaseR hbase2 hlarge)
    have hqlo := hm (htime _ hbase).1 hAl
      (hstrict.monotoneOn hbase hbaseL hsmall)
    have hw := hwindow (time (2 * S)) (time (a * S))
      (zero_le_one.trans (hA.trans (htime _ hbase2).1))
      (zero_le_one.trans (hA.trans (htime _ hbase).1))
      (htime _ hbase2).2 (htime _ hbase).2
    exact hqhi.trans (hw.trans (mul_le_mul_of_nonneg_left hqlo (zero_le_one.trans hK)))
  have hqpos : ∀ t ∈ Set.Icc tl tr, 0 < clockSpeed o h t := by
    intro t ht
    exact mul_pos (htl.trans_le ht.1)
      (scalar_pos X o h hH (htl.le.trans ht.1) o)
  have hlog : Real.log (clockSpeed o h tr) - Real.log (clockSpeed o h tl) ≤ Real.log K := by
    have hqp := hqpos tl (Set.left_mem_Icc.mpr hlr.le)
    have hqpr := hqpos tr (Set.right_mem_Icc.mpr hlr.le)
    have hh := Real.log_le_log hqpr hqwindow
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hK)) hqp.ne'] at hh
    linarith
  have hscont : ContinuousOn (ρ o) (Set.Icc tl tr) := by
    intro t ht
    exact (rho_hasDerivAt X o h U P ρ hf o (htl.trans_le ht.1)).continuousAt.continuousWithinAt
  have hqcont : ContinuousOn (clockSpeed o h) (Set.Icc tl tr) := by
    intro t ht
    exact (continuousAt_id.mul
      (scalar_contDiffAt X o h U P ρ hf o (htl.trans_le ht.1)).continuousAt).continuousWithinAt
  obtain ⟨tw, htw, hratio⟩ := exists_log_deriv_ratio_point hlr hscont hqcont hqpos
    (fun t ht => rho_hasDerivAt X o h U P ρ hf o (htl.trans ht.1))
    (fun t ht => differentiableAt_id.mul
      ((scalar_contDiffAt X o h U P ρ hf o (htl.trans ht.1)).differentiableAt (by simp)))
    (fun t ht => scalar_pos X o h hH (htl.le.trans ht.1.le) o)
    (by rw [hsl, hsr]; exact hmiddle)
  have htwpos : 0 < tw := htl.trans htw.1
  have hqtw : 0 < clockSpeed o h tw := hqpos tw (Set.Ioo_subset_Icc_self htw)
  have hrtw := scalar_pos X o h hH htwpos.le o
  have hsm := rho_strictMonoOn_nonneg X o h U P ρ hf hH
  refine ⟨tw, htwpos, ?_, ?_, ?_, ?_⟩
  · rw [← hsl]
    exact hsm.monotoneOn htl.le htwpos.le htw.1.le
  · rw [← hsr]
    exact hsm.monotoneOn htwpos.le htr.le htw.2.le
  · exact div_nonneg (clockSpeed_deriv_nonneg X o h U P ρ hf hH htwpos)
      (mul_pos hqtw hrtw).le
  · rw [hsl, hsr] at hratio
    rw [hratio]
    have hgap : 7 * S / 4 - 5 * S / 4 = S / 2 := by ring
    rw [hgap]
    apply (div_le_iff₀ (half_pos hS)).mpr
    have hc : (2 * Real.log K / S) * (S / 2) = Real.log K := by field_simp
    rw [hc]
    exact hlog

end Yau.Proofs.C04Aux
