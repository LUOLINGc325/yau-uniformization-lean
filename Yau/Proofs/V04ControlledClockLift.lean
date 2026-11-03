import Yau.Proofs.V04ClockWeightSeminorm
import Yau.Proofs.V04ClockLiftSeminorm

/-! A single actual clock lift has uniform weight and half-order bounds
on minimizing tails; its constant is chosen before penalties and families. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem fixed_index_controlled_clockLift {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ F : ℕ → VariationDisc X, MinimizingSequence d j ε F →
        ∀ᶠ ν in atTop, ∃ Γ : ℂ → ℂ,
          ClockLift d k j a (F ν) Γ ∧
          (∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ 1 + (Γ z).re) ∧
          (∀ θ, clockWeight d k j a (F ν) θ ≤ C) ∧
          boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ)) ≤
            ENNReal.ofReal C * variationEnergy d j (F ν) := by
  obtain ⟨C₀, hC₀, hsemi⟩ := fixed_index_clock_weight_seminorm_bound hd hk j a
  obtain ⟨z, hz, hZ⟩ := fixed_index_clock_normalizer_lower hd hk j a
  let C := 1 + 2 * C₀ + z⁻¹
  have hC : 1 ≤ C := by dsimp only [C]; linarith [inv_nonneg.mpr hz.le]
  refine ⟨C, hC, fun ε hε hε1 F hF => ?_⟩
  filter_upwards [hsemi ε hε hε1 F hF, hZ ε hε hε1 F hF] with ν hνsemi hνZ
  let γ := clockWeight d k j a (F ν)
  have hraw := clockWeightRaw_contDiff (a := a) hd hk (hF.1 ν)
  have hγ : ContDiff ℝ ∞ γ := hraw.div_const _
  have hgp : Function.Periodic γ (2 * Real.pi) := by
    intro θ
    simp only [γ, clockWeight, clockWeightRaw_periodic d k j a (F ν) θ]
  have hn := clockWeight_normalization (a := a) hd (hF.1 ν) hraw.continuous
  have hs := clockLiftCandidate_smooth hγ hgp
  have hb := clockLiftCandidate_zero_real_boundary hγ hgp hn.2
  refine ⟨clockLiftCandidate γ, ⟨hs, hb.1, hb.2⟩, ?_, ?_, ?_⟩
  · apply closedDisc_real_part_lower hs
    intro θ
    rw [hb.2 θ]
    linarith only [(hn.1 θ).le]
  · intro θ
    have hZp := clockWeightRaw_average_pos (a := a) hd (hF.1 ν) hraw.continuous
    have hi := inv_anti₀ hz hνZ
    have hr := div_le_div_of_nonneg_right (clockWeightRaw_le_one (a := a) hd hk (hF.1 ν) θ) hZp.le
    change clockWeightRaw d k j a (F ν) θ /
      circleAverage (clockWeightRaw d k j a (F ν)) ≤ C
    rw [one_div] at hr
    have hz0 := inv_nonneg.mpr hz.le
    dsimp only [C]
    linarith only [hr, hi, hz0, hC₀]
  · calc
      _ ≤ 2 * scalarDSq γ := clockLiftCandidate_boundaryDSq_le hγ hgp hn.2
      _ ≤ 2 * (ENNReal.ofReal C₀ * variationEnergy d j (F ν)) :=
        mul_le_mul_of_nonneg_left hνsemi (by norm_num)
      _ = ENNReal.ofReal (2 * C₀) * variationEnergy d j (F ν) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
        ring
      _ ≤ ENNReal.ofReal C * variationEnergy d j (F ν) := by
        gcongr
        dsimp only [C]
        linarith [inv_nonneg.mpr hz.le]

end Yau.Blueprint.V04Proof
