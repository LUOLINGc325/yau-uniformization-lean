import Yau.Proofs.P06ScalarUniquenessTrace

/-! The terminal energy estimate for arbitrary bounded classical scalar heat.
The compact initial term is removed with the original continuous trace. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- A larger cutoff equal to one on the smaller support controls its actual
boundary energy by the larger localized square. -/
theorem scalarHeat_cutoff_error_le
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {w η ψ : M.Carrier → ℝ} (hw : SmoothFn w)
    (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ)
    (hone : ∀ x ∈ tsupport η, ψ x = 1)
    {a : ℝ} (ha : 0 ≤ a)
    (hgrad : ∀ x, scalarGradientPair g.form η η x ≤ a) :
    (∫ x, w x ^ 2 * scalarGradientPair g.form η η x ∂μ) ≤
      a * ∫ x, ψ x ^ 2 * w x ^ 2 ∂μ := by
  have hi : Integrable (fun x => w x ^ 2 * scalarGradientPair g.form η η x) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hw 2) (smoothFn_scalarGradientPair g hη hη))
      (scalarGradientPair_hasCompactSupport g.form η η hcη).mul_left
  have hj : Integrable (fun x => ψ x ^ 2 * w x ^ 2) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hψ 2) (smoothFn_pow hw 2))
      (by
        have hs : HasCompactSupport (fun x => ψ x * ψ x) := hcψ.mul_right
        have hs' : HasCompactSupport (fun x => (ψ x * ψ x) * w x ^ 2) := hs.mul_right
        simpa only [← pow_two] using hs')
  rw [← integral_const_mul]
  apply integral_mono hi (hj.const_mul a)
  intro x
  change w x ^ 2 * scalarGradientPair g.form η η x ≤ a * (ψ x ^ 2 * w x ^ 2)
  by_cases hx : x ∈ tsupport η
  · simpa only [hone x hx, one_pow, one_mul, mul_comm a] using
      mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg (w x))
  · rw [scalarGradientPair_zero_of_notMem_tsupport g.form η η hx, mul_zero]
    positivity

/-- Retaining the terminal term in genuine Caccioppoli gives the local
energy inequality for a zero continuous initial trace. -/
theorem continuousInitialHeat_cutoff_energy_le
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    {u : ℝ → M.Carrier → ℝ}
    (hu : IsContinuousInitialScalarHeat g.form 0 u)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηbound : ∀ x, |η x| ≤ 1)
    {Q T : ℝ} (hQ : 0 ≤ Q) (hT : 0 < T)
    (herror : ∀ s, 0 < s → s ≤ T →
      (∫ x, u s x ^ 2 * scalarGradientPair g.form η η x ∂μ) ≤ Q) :
    ∀ t, 0 < t → t ≤ T → (∫ x, η x ^ 2 * u t x ^ 2 ∂μ) ≤ 2 * T * Q := by
  intro t ht htT
  have hlim := (continuousInitialHeat_cutoff_energy_tendsto_zero g μ hμ hu hη hcη hηbound).add_const (2 * T * Q)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [zero_add] using hlim)
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  have hslab : Icc s t ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_lt_of_le hs.1 hr.1
  have hreg := LocalTime.scalarHeat_cutoff_integrable isOpen_Ioi g μ hμ hu.2.1 hη hcη hslab hs.2.le
  have hcap := LocalTime.scalarHeat_caccioppoli_signed isOpen_Ioi g hK μ hμ hu.2.1
    1 (by norm_num) (fun x r hr => by simpa only [one_mul] using hu.2.2.1 x r hr)
    hη hcη hslab hs.2.le
  have hgrad : 0 ≤ ∫ r in s..t, ∫ x, η x ^ 2 *
      scalarGradientPair g.form (u r) (u r) x ∂μ := by
    apply intervalIntegral.integral_nonneg hs.2.le
    intro r _
    exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (scalarGradientPair_self_nonneg _ _ _))
  have herr : (∫ r in s..t, ∫ x, u r x ^ 2 * scalarGradientPair g.form η η x ∂μ) ≤
      (t - s) * Q := by
    have hh := intervalIntegral.integral_mono_on hs.2.le hreg.2.2
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Q) volume s t)
      (fun r hr => herror r (hslab hr) (hr.2.trans htT))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  have htime : (t - s) * Q ≤ T * Q := mul_le_mul_of_nonneg_right (by linarith [hs.1]) hQ
  simp only [mul_one] at hcap
  nlinarith

end Yau.NodeProofs.P06Aux
