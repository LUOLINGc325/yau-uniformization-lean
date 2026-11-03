import Yau.Proofs.V04ClockWallPointwise
import Yau.Proofs.V04SymplecticScalarRegularity
import Yau.Proofs.V04ClockLossLocalization

/-! Average the genuine pointwise wall comparison only at continuous
computed integrands. Its damping tends to zero in the outer index. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockErrorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.Blueprint.V04Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem clock_damping_tendsto (c : ℕ) (hc : 0 < c) :
    Tendsto (fun j : ℕ => ((j + 3 : ℝ) ^ c)⁻¹) atTop (𝓝 0) := by
  have hJ : Tendsto (fun j : ℕ => (j + 3 : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro j
    linarith
  have hp : Tendsto (fun j : ℕ => (j + 3 : ℝ) ^ c) atTop atTop := by
    apply tendsto_atTop_mono _ hJ
    intro j
    apply le_self_pow₀ _ hc.ne'
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith
  exact tendsto_inv_atTop_zero.comp hp

theorem clockWall_cost_comparison_of_continuous {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hFiber : FiberWallError d k) (hBase : BaseWallError d k)
    {a : ℕ} (ha : 3 ≤ 4 * a) (hpa : k.fiberPower ≤ 4 * a) (hpc : k.fiberPower ≤ k.dampingPower) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (F : VariationDisc X), AdmissibleVariationDisc d j F →
      Continuous (clockBoundaryDensity d k j a F) →
      clockSymplecticCost d k j a F ≤ clockBoundaryCost d k j a F +
        C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ / circleAverage (clockWeightRaw d k j a F) := by
  obtain ⟨C, hC, hpoint⟩ := clockWall_pointwise_comparison hd hk hFiber hBase ha hpa hpc
  refine ⟨C, hC, fun j F hF hb => ?_⟩
  have ht := (admissible_discTime_trace_contDiff hF).continuous
  have hγ : Continuous (clockWeight d k j a F) := (clockWeightRaw_contDiff hd hk hF).continuous.div_const _
  have hs := boundarySymplectic_continuous hd hF
  have hl : Continuous (fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
      symplecticP (boundaryHessian d j F (circlePoint θ))) := (ht.div_const F.s).mul hγ |>.mul hs
  have hh := circleAverage_mono_of_continuous hl (hb.add continuous_const) (hpoint j F hF)
  change circleAverage (fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
      symplecticP (boundaryHessian d j F (circlePoint θ))) ≤
    circleAverage (fun θ => clockBoundaryDensity d k j a F θ +
      C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ / circleAverage (clockWeightRaw d k j a F)) at hh
  rw [circleAverage_add_of_continuous hb continuous_const, circleAverage_const_value] at hh
  exact hh

theorem clockWall_fourth_of_continuous {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hFiber : FiberWallError d k) (hBase : BaseWallError d k)
    {a : ℕ} (ha : 3 ≤ 4 * a) (hpa : k.fiberPower ≤ 4 * a) (hpc : k.fiberPower ≤ k.dampingPower)
    (hc : 0 < k.dampingPower) (hloc : LocalizationEstimates d)
    (hcontinuous : ∀ j (F : VariationDisc X), AdmissibleVariationDisc d j F →
      Continuous (clockBoundaryDensity d k j a F))
    {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    ∀ r, 0 < r → ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      clockSymplecticCost d k j a (F j ε ν) ≤ clockBoundaryCost d k j a (F j ε ν) + r := by
  obtain ⟨C, hC, hcost⟩ := clockWall_cost_comparison_of_continuous hd hk hFiber hBase ha hpa hpc
  have hloss := (clockNormalization_losses_localized hd hk hloc a hF).1
  intro r hr
  have hsmall := ((clock_damping_tendsto k.dampingPower hc).const_mul (2 * C)).eventually
    (Iio_mem_nhds (by simpa only [mul_zero] using hr))
  filter_upwards [hloss (1 / 2) (by norm_num), hsmall, hF] with j hjZ hjrate hjF
  filter_upwards [hjZ, hjF] with ε hεZ hεF
  filter_upwards [hεZ] with ν hνZ
  have hA := hεF.1 ν
  have hZ : 0 < circleAverage (clockWeightRaw d k j a (F j ε ν)) :=
    clockWeightRaw_average_pos hd hA (clockWeightRaw_contDiff hd hk hA).continuous
  have hZhalf : 1 / 2 ≤ circleAverage (clockWeightRaw d k j a (F j ε ν)) := by
    have hh := (abs_le.mp hνZ).1
    linarith only [hh]
  have hJ : 0 ≤ ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by positivity
  have herr : C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ /
      circleAverage (clockWeightRaw d k j a (F j ε ν)) ≤ r := by
    apply (div_le_iff₀ hZ).2
    have hh := mul_le_mul_of_nonneg_left hZhalf hr.le
    have hrate : 2 * C * ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ < r := hjrate
    nlinarith only [hh, hrate]
  exact (hcost j (F j ε ν) hA (hcontinuous j (F j ε ν) hA)).trans (by linarith only [herr])

end Yau.Blueprint.V04Proof.ClockErrorAux
