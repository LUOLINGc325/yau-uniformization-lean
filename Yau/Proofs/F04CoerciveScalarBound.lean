import Yau.LeafProofs.L16GalerkinEnergy

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

/-- Constants fixed before the forcing and the Galerkin space. -/
def coerciveTimeBound (T K : ℝ) : ℝ := Real.exp (K * T)
def coerciveEnergyBound (T α K : ℝ) : ℝ :=
  (1 + K * T * coerciveTimeBound T K) / α

theorem coercive_scalar_uniform_bound {T α K : ℝ} (hT : 0 < T) (hα : 0 < α) (hK : 0 < K)
    {y z q : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hy0 : ∀ t ∈ Icc 0 T, 0 ≤ y t) (hz0 : ∀ t ∈ Icc 0 T, 0 ≤ z t)
    (hq : IntervalIntegrable q volume 0 T) (hq0 : ∀ t, 0 ≤ q t)
    (henergy : ∀ t ∈ Icc 0 T, y t + α * (∫ s in (0 : ℝ)..t, z s) ≤
      K * (∫ s in (0 : ℝ)..t, y s) + ∫ s in (0 : ℝ)..t, q s) :
    (∀ t ∈ Icc 0 T, y t ≤ coerciveTimeBound T K * (∫ s in (0 : ℝ)..T, q s)) ∧
    (∫ s in (0 : ℝ)..T, z s) ≤ coerciveEnergyBound T α K * (∫ s in (0 : ℝ)..T, q s) := by
  let E := coerciveTimeBound T K
  let Q := ∫ s in (0 : ℝ)..T, q s
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg_of_forall hT.le hq0
  have hyi : IntervalIntegrable y volume 0 T := hy.intervalIntegrable_of_Icc hT.le
  have hpre : ∀ t ∈ Icc 0 T, y t ≤ K * (∫ s in (0 : ℝ)..t, y s) + Q := by
    intro t ht
    have hzint : 0 ≤ ∫ s in (0 : ℝ)..t, z s :=
      intervalIntegral.integral_nonneg ht.1 (fun s hs => hz0 s ⟨hs.1, hs.2.trans ht.2⟩)
    have hqm : (∫ s in (0 : ℝ)..t, q s) ≤ Q :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Eventually.of_forall hq0) hq
    have he := henergy t ht
    have hαz := mul_nonneg hα.le hzint
    dsimp only [Q] at *
    linarith
  have hpoint : ∀ t ∈ Icc 0 T, y t ≤ E * Q := by
    intro t ht
    calc
      y t ≤ Real.exp (K * t) * Q :=
        Yau.LeafProofs.L16Aux.energy_integral_gronwall_on hT.le hK hy hpre t ht
      _ ≤ E * Q := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK.le)) hQ
  have hyint : (∫ s in (0 : ℝ)..T, y s) ≤ T * E * Q := by
    calc
      _ ≤ ∫ _s in (0 : ℝ)..T, E * Q :=
        intervalIntegral.integral_mono_on hT.le hyi intervalIntegrable_const hpoint
      _ = T * E * Q := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
  refine ⟨hpoint, ?_⟩
  have hzend := henergy T ⟨hT.le, le_rfl⟩
  have hyT := hy0 T ⟨hT.le, le_rfl⟩
  have hm := mul_le_mul_of_nonneg_left hyint hK.le
  apply (mul_le_mul_iff_right₀ hα).mp
  have heq : α * (coerciveEnergyBound T α K * Q) = (1 + K * T * E) * Q := by
    unfold coerciveEnergyBound E
    field_simp
  rw [heq]
  dsimp only [Q] at *
  nlinarith

end Yau.F04Proof
