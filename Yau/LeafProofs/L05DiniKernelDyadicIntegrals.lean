import Yau.LeafProofs.L05DiniKernelDyadicData
import Yau.LeafProofs.L05DiniKernelScaleParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem dini_integral_tsum_le_two {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {F : ℕ → X → ℝ} {M : ℝ} (_hM : 0 ≤ M) (hF : ∀ i, Integrable (F i) mu)
    (hF0 : ∀ i, 0 ≤ᵐ[mu] F i) (hBound : ∀ i, (∫ x, F i x ∂mu) ≤ M*(1/2:ℝ)^i) :
    (∫ x, ∑' i, F i x ∂mu) ≤ 2*M := by
  have hNormEq (i : ℕ) : (∫ x, ‖F i x‖ ∂mu)=(∫ x, F i x ∂mu) :=
    integral_congr_ae ((hF0 i).mono (fun x hx => Real.norm_of_nonneg hx))
  have hGeom := (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_left M
  have hNormSum : Summable (fun i => ∫ x, ‖F i x‖ ∂mu) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _))
      (fun i => (hNormEq i).trans_le (hBound i)) hGeom
  have hSum : Summable (fun i => ∫ x, F i x ∂mu) := hNormSum.congr hNormEq
  have hSwap := integral_tsum_of_summable_integral_norm hF hNormSum
  have hh := hSum.tsum_le_tsum hBound hGeom
  rw [hSwap,tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)] at hh
  exact hh.trans_eq (by norm_num; ring)

set_option maxHeartbeats 1800000 in
theorem diniDyadicAverage_near_le {psi : ℝ → ℝ} {eta B R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hR : 0 < R) :
    (∫ s in (0:ℝ)..R, diniDyadicAverage psi s/s) ≤ 2*diniBudget psi R := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc 0 R)
  let F := fun (i : ℕ) (s : ℝ) => (1/4:ℝ)^i*(psi ((2:ℝ)^i*s)/s)
  have hM : 0 ≤ diniBudget psi R := diniBudget_nonneg hR (fun s hs => (hpsi s hs).1)
  have hFI (i : ℕ) : Integrable (F i) mu := by
    have hc : 0 < (2:ℝ)^i := pow_pos (by norm_num) _
    have hd := dini_comp_mul_data hB hm hc hpsi
    exact (diniBudget_integrable he he1 hd.2.1 hd.1 hd.2.2 hR).1.1.const_mul _
  have hF0 (i : ℕ) : 0 ≤ᵐ[mu] F i := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (div_nonneg (hpsi _ (mul_pos (pow_pos (by norm_num) _) hs.1)).1 hs.1.le)
  have hBound (i : ℕ) : (∫ s, F i s ∂mu) ≤ diniBudget psi R*(1/2:ℝ)^i := by
    have hc : 0 < (2:ℝ)^i := pow_pos (by norm_num) _
    have hc1 : 1 ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num)
    have hq : 0 ≤ (1/4:ℝ)^i := pow_nonneg (by norm_num) _
    have hGeom : (1/4:ℝ)^i*(2:ℝ)^i=(1/2:ℝ)^i := by rw [← mul_pow]; norm_num
    calc
      _=(1/4:ℝ)^i*(∫ s in (0:ℝ)..R, psi ((2:ℝ)^i*s)/s) := by
        rw [intervalIntegral.integral_of_le hR.le]
        exact integral_const_mul _ _
      _=(1/4:ℝ)^i*(∫ s in (0:ℝ)..(2:ℝ)^i*R, psi s/s) := by
        rw [dini_near_comp_mul he he1 hB hm hpsi hc hR]
      _≤(1/4:ℝ)^i*diniBudget psi ((2:ℝ)^i*R) :=
        mul_le_mul_of_nonneg_left (dini_near_le_budget (mul_pos hc hR) (fun s hs => (hpsi s hs).1)) hq
      _≤(1/4:ℝ)^i*((2:ℝ)^i*diniBudget psi R) :=
        mul_le_mul_of_nonneg_left (diniBudget_dilate_le he he1 hB hm hpsi hR hc1) hq
      _=diniBudget psi R*(1/2:ℝ)^i := by rw [← hGeom]; ring
  have hPoint (s : ℝ) : (∑' i, F i s)=diniDyadicAverage psi s/s := by
    calc
      _=∑' i : ℕ, ((1/4:ℝ)^i*psi ((2:ℝ)^i*s))/s := tsum_congr (fun i => by dsimp only [F]; ring)
      _=_ := tsum_div_const
  have hh := dini_integral_tsum_le_two hM hFI hF0 hBound
  rw [intervalIntegral.integral_of_le hR.le]
  exact (integral_congr_ae (ae_of_all _ fun s => (hPoint s).symm)).trans_le hh

set_option maxHeartbeats 1800000 in
theorem diniDyadicAverage_far_le {psi : ℝ → ℝ} {eta B R : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hR : 0 < R) :
    (∫ s in Set.Ioi R, diniDyadicAverage psi s/s^2) ≤ 2*(∫ s in Set.Ioi R, psi s/s^2) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi R)
  let F := fun (i : ℕ) (s : ℝ) => (1/4:ℝ)^i*(psi ((2:ℝ)^i*s)/s^2)
  have hM : 0 ≤ ∫ s in Set.Ioi R, psi s/s^2 := dini_far_nonneg hR (fun s hs => (hpsi s hs).1)
  have hFI (i : ℕ) : Integrable (F i) mu := by
    have hc : 0 < (2:ℝ)^i := pow_pos (by norm_num) _
    have hd := dini_comp_mul_data hB hm hc hpsi
    exact (diniBudget_integrable he he1 hd.2.1 hd.1 hd.2.2 hR).2.const_mul _
  have hF0 (i : ℕ) : 0 ≤ᵐ[mu] F i := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (div_nonneg (hpsi _ (mul_pos (pow_pos (by norm_num) _) (hR.trans hs))).1 (sq_nonneg _))
  have hBound (i : ℕ) : (∫ s, F i s ∂mu) ≤ (∫ s in Set.Ioi R, psi s/s^2)*(1/2:ℝ)^i := by
    have hc : 0 < (2:ℝ)^i := pow_pos (by norm_num) _
    have hc1 : 1 ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num)
    have hq : 0 ≤ (1/4:ℝ)^i := pow_nonneg (by norm_num) _
    have hGeom : (1/4:ℝ)^i*(2:ℝ)^i=(1/2:ℝ)^i := by rw [← mul_pow]; norm_num
    have hRc : R ≤ (2:ℝ)^i*R := by nlinarith only [hc1,hR]
    calc
      _=(1/4:ℝ)^i*(∫ s in Set.Ioi R, psi ((2:ℝ)^i*s)/s^2) := integral_const_mul _ _
      _=(1/4:ℝ)^i*((2:ℝ)^i*(∫ s in Set.Ioi ((2:ℝ)^i*R), psi s/s^2)) := by
        rw [dini_far_comp_mul he he1 hB hm hpsi hc hR]
      _≤(1/4:ℝ)^i*((2:ℝ)^i*(∫ s in Set.Ioi R, psi s/s^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dini_far_antitone he he1 hB hm hpsi hR hRc) hc.le) hq
      _=(∫ s in Set.Ioi R, psi s/s^2)*(1/2:ℝ)^i := by rw [← hGeom]; ring
  have hPoint (s : ℝ) : (∑' i, F i s)=diniDyadicAverage psi s/s^2 := by
    calc
      _=∑' i : ℕ, ((1/4:ℝ)^i*psi ((2:ℝ)^i*s))/s^2 := tsum_congr (fun i => by dsimp only [F]; ring)
      _=_ := tsum_div_const
  have hh := dini_integral_tsum_le_two hM hFI hF0 hBound
  exact (integral_congr_ae (ae_of_all _ fun s => (hPoint s).symm)).trans_le hh

end Yau.LeafProofs.L05Aux
