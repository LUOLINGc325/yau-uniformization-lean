import Yau.LeafProofs.L05DiniKernelScalarIntegrals
import Yau.LeafProofs.L05DiniKernelBudgetScale

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem dini_comp_mul_data {psi : ℝ → ℝ} {eta B c : ℝ} (hB : 0 ≤ B)
    (hm : Measurable psi) (hc : 0 < c)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) :
    Measurable (fun s : ℝ => psi (c*s)) ∧ 0 ≤ B*c^eta ∧
      (∀ s : ℝ, 0 < s → 0 ≤ psi (c*s) ∧ psi (c*s) ≤ (B*c^eta)*s^eta) := by
  refine ⟨hm.comp (measurable_const.mul measurable_id),mul_nonneg hB (Real.rpow_nonneg hc.le _),?_⟩
  intro s hs
  have hh := hpsi (c*s) (mul_pos hc hs)
  rw [Real.mul_rpow hc.le hs.le] at hh
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩

theorem dini_near_comp_mul {psi : ℝ → ℝ} {eta B c r : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hc : 0 < c) (hr : 0 < r) :
    (∫ s in (0:ℝ)..r, psi (c*s)/s)=(∫ s in (0:ℝ)..c*r, psi s/s) := by
  have hd := dini_comp_mul_data hB hm hc hpsi
  have h1 := dini_recent_scalar_change he he1 hB hm hpsi hc hr
  have h2 := dini_recent_scalar_change he he1 hd.2.1 hd.1 hd.2.2 zero_lt_one hr
  simp only [one_mul] at h2
  linarith only [h1,h2]

theorem dini_far_comp_mul {psi : ℝ → ℝ} {eta B c r : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) (hc : 0 < c) (hr : 0 < r) :
    (∫ s in Set.Ioi r, psi (c*s)/s^2)=c*(∫ s in Set.Ioi (c*r), psi s/s^2) := by
  have hd := dini_comp_mul_data hB hm hc hpsi
  have h1 := dini_old_scalar_change he he1 hB hm hpsi hc hr
  have h2 := dini_old_scalar_change he he1 hd.2.1 hd.1 hd.2.2 zero_lt_one hr
  simp only [one_mul,mul_one] at h2
  nlinarith only [h1,h2]

theorem dini_far_nonneg {psi : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s) : 0 ≤ ∫ s in Set.Ioi r, psi s/s^2 := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact div_nonneg (hpsi s (hr.trans hs)) (sq_nonneg _)

theorem dini_near_le_budget {psi : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hpsi : ∀ s : ℝ, 0 < s → 0 ≤ psi s) : (∫ s in (0:ℝ)..r, psi s/s) ≤ diniBudget psi r := by
  exact le_add_of_nonneg_right (mul_nonneg hr.le (dini_far_nonneg hr hpsi))

theorem dini_far_antitone {psi : ℝ → ℝ} {eta B r s : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable psi)
    (hpsi : ∀ a : ℝ, 0 < a → 0 ≤ psi a ∧ psi a ≤ B*a^eta) (hr : 0 < r) (hrs : r ≤ s) :
    (∫ a in Set.Ioi s, psi a/a^2) ≤ (∫ a in Set.Ioi r, psi a/a^2) := by
  apply setIntegral_mono_set (diniBudget_integrable he he1 hB hm hpsi hr).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact div_nonneg (hpsi a (hr.trans ha)).1 (sq_nonneg _)
  · exact Filter.Eventually.of_forall (fun a ha => hrs.trans_lt ha)

end Yau.LeafProofs.L05Aux
