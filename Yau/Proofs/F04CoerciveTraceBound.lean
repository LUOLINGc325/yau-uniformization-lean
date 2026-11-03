import Yau.Proofs.F04CoerciveScalarBound
import Yau.Proofs.F04DualPairing

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

/-- The actual closed-time energy chain gives the uniform pivot bound for the
 original continuous trace and one coercive L2 shift. -/
theorem coercive_trace_uniform_bound
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T α shift : ℝ} (hT : 0 < T) (hα : 0 < α) (hshift : 0 ≤ shift)
    (j : V →L[ℝ] H) (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hGard : ∀ t ∈ Icc 0 T, ∀ v : V, α * ‖v‖ ^ 2 ≤ B t v v + shift * ‖j v‖ ^ 2)
    {F : ℝ → H} {U : ℝ → V} {R : ℝ → StrongDual ℝ V} {a : ℝ → H}
    (hF : MemLp F 2 (volume.restrict (Ioo 0 T)))
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (ha : ContinuousOn a (Icc 0 T)) (ha0 : a 0 = 0)
    (hAE : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = a t)
    (hChain : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ‖a t‖ ^ 2 - ‖a s‖ ^ 2 = 2 * ∫ r in s..t, R r (U r))
    (hEq : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : V, R t v + B t (U t) v = inner ℝ (F t) (j v)) :
    ∀ t ∈ Icc 0 T, ‖a t‖ ^ 2 ≤ coerciveTimeBound T (2 * shift + 1) * (∫ s in Ioo 0 T, ‖F s‖ ^ 2) := by
  let y := fun t => ‖a t‖ ^ 2
  let p := fun t => 2 * R t (U t)
  let q := fun t => ‖F t‖ ^ 2
  let K := 2 * shift + 1
  let Q := ∫ s in Ioo 0 T, q s
  have hK : 0 < K := by dsimp only [K]; positivity
  have hy : ContinuousOn y (Icc 0 T) := ha.norm.pow 2
  have hp : IntegrableOn p (Ioo 0 T) := (dualPairing_integrable_L2 hU hR).const_mul 2
  have hq : IntegrableOn q (Ioo 0 T) := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  have hPoint : p ≤ᵐ[volume.restrict (Ioo 0 T)] (fun t => K * y t + q t) := by
    filter_upwards [hEq, hAE, ae_restrict_mem measurableSet_Ioo] with t het hat ht
    have he := het (U t)
    have hc := hGard t (Ioo_subset_Icc_self ht) (U t)
    rw [hat] at he hc
    have hi := real_inner_le_norm (F t) (a t)
    have hs := sq_nonneg (‖F t‖ - ‖a t‖)
    have hα0 : 0 ≤ α * ‖U t‖ ^ 2 := mul_nonneg hα.le (sq_nonneg _)
    change 2 * R t (U t) ≤ (2 * shift + 1) * ‖a t‖ ^ 2 + ‖F t‖ ^ 2
    nlinarith only [he, hc, hi, hs, hα0]
  have hPre : ∀ t ∈ Icc 0 T, y t ≤ K * (∫ s in (0 : ℝ)..t, y s) + Q := by
    intro t ht
    have hyi : IntervalIntegrable y volume 0 t :=
      (hy.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hyt := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp hyi
    have hpt := hp.mono_set (Ioo_subset_Ioo le_rfl ht.2)
    have hqt := hq.mono_set (Ioo_subset_Ioo le_rfl ht.2)
    have hcmp := integral_mono_ae hpt ((hyt.const_mul K).add hqt)
      (hPoint.filter_mono (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2) le_rfl)))
    have hAdd : (∫ s in Ioo 0 t, K * y s + q s) = K * (∫ s in Ioo 0 t, y s) + ∫ s in Ioo 0 t, q s := by
      rw [integral_add (hyt.const_mul K) hqt, integral_const_mul]
    simp only [Pi.add_apply] at hcmp
    rw [hAdd] at hcmp
    have hqi : IntervalIntegrable q volume 0 T := (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hq
    have hqm : (∫ s in (0 : ℝ)..t, q s) ≤ Q := by
      have hm := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall (fun s => sq_nonneg ‖F s‖)) hqi
      simpa only [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo, Q] using hm
    have he := hChain 0 ⟨le_rfl, hT.le⟩ t ht
    rw [ha0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at he
    have he' : y t = ∫ s in (0 : ℝ)..t, p s := by
      simpa only [p, y, intervalIntegral.integral_const_mul] using he
    have hcmp' : (∫ s in (0 : ℝ)..t, p s) ≤ K * (∫ s in (0 : ℝ)..t, y s) + ∫ s in (0 : ℝ)..t, q s := by
      simpa only [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo] using hcmp
    linarith only [he', hcmp', hqm]
  intro t ht
  calc
    y t ≤ Real.exp (K * t) * Q := Yau.LeafProofs.L16Aux.energy_integral_gronwall_on hT.le hK hy hPre t ht
    _ ≤ coerciveTimeBound T K * Q := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK.le)) hQ

end Yau.F04Proof
