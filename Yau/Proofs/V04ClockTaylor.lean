import Yau.Proofs.V04ClockTaylorFunctional
import Yau.Proofs.V04ClockTaylorQuotient
import Yau.Proofs.V04ControlledClockLift
import Yau.Proofs.V02InfimumTest

/-! The fifth original ClockEstimates clause. Its energy coefficient is
chosen before the family; the sequence limit precedes the backward increment. -/
open Filter Set
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem minimizing_energy_cap {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {ε : ℝ} (hε : 0 < ε) {F : ℕ → VariationDisc X}
    (hF : MinimizingSequence d j ε F) :
    ∃ E₀ : ℝ, 0 ≤ E₀ ∧ ∀ᶠ ν in atTop, (variationEnergy d j (F ν)).toReal ≤ E₀ := by
  have hgap := V02Proof.minimizingSequence_gap_tendsto hd hε.le hF
  let E₀ := max 0 (((localizedInfimum d j ε).toReal + 1) / ε)
  refine ⟨E₀, le_max_left _ _, ?_⟩
  filter_upwards [hgap.eventually (Iio_mem_nhds zero_lt_one)] with ν hν
  have hl := penalizedFunctional_lower_wall_energy hd (hF.1 ν) ε
  have hw := admissible_wallAverage_nonneg hd (hF.1 ν)
  have he : (variationEnergy d j (F ν)).toReal ≤ ((localizedInfimum d j ε).toReal + 1) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  exact he.trans (le_max_right _ _)

theorem clockEstimates_fifth {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (hloc : LocalizationEstimates d) (a : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ F : ℕ → ℝ → ℕ → VariationDisc X, LocalizedMinimizers d F →
        ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          SeqUpperZero (fun ν => clockBoundaryCost d k j a (F j ε ν) -
            deriv (d.test ((F j ε ν).f 0)) (F j ε ν).s -
            C j * ε * (1 + (variationEnergy d j (F j ε ν)).toReal)) := by
  classical
  choose G hG hcontrol using fun j => fixed_index_controlled_clockLift hd hk j a
  obtain ⟨s₀, hs₀, htime⟩ := setup_center_time_lower hd
  let C : ℕ → ℝ := fun j => (1 / 2 + Real.pi * G j) / s₀
  have hG0 (j : ℕ) : 0 ≤ G j := by linarith [hG j]
  have hC (j : ℕ) : 0 ≤ C j :=
    div_nonneg (add_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le (hG0 j))) hs₀.le
  obtain ⟨Kc, hKc, hKcO, hcenters⟩ := uniform_minimizing_centers hd hloc
  refine ⟨C, hC, fun F hF => ?_⟩
  filter_upwards [hF, hcenters] with j hmin hcenter
  have hεle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hmin, hcenter, self_mem_nhdsWithin, hεle] with ε hmin hcenter hε hε1
  obtain ⟨M, hM, hcost⟩ := fixed_index_boundary_cost_cap hd j
  obtain ⟨E₀, hE₀, henergy⟩ := minimizing_energy_cap hd hε hmin
  obtain ⟨r, R, hr, hr1, hR, hTaylor⟩ := whole_functional_backward_taylor hd hk j a hKc hKcO
    (C := G j) (M := M) (E₀ := E₀) (ε := ε) (by linarith [hG j])
    (by linarith [hM]) hE₀ hε.le
  let gap : ℕ → ℝ := fun ν => penalizedFunctional d j ε (F j ε ν) - (localizedInfimum d j ε).toReal
  have hgap : Tendsto (fun ν => gap ν / s₀) atTop (𝓝 0) := by
    simpa only [zero_div] using (V02Proof.minimizingSequence_gap_tendsto hd hε.le hmin).div_const s₀
  apply seqUpperZero_of_linear_quotients hgap
  refine ⟨r, R / s₀, hr, div_nonneg hR hs₀.le, fun ρ hρ hρr => ?_⟩
  filter_upwards [hcontrol j ε hε hε1 (F j ε) hmin, hcenter (F j ε) hmin,
    hcost ε hε hε1 (F j ε) hmin, henergy] with ν hΓ hc hcost he
  obtain ⟨Γ, hΓ, hβ, hγ, hΓD⟩ := hΓ
  have hu : -ρ ∈ Icc (-r) 0 := ⟨by linarith, by linarith⟩
  have ht := hTaylor (F j ε ν) (hmin.1 ν) hc hcost he Γ hΓ hβ hγ hΓD (-ρ) hu
  have hlower := V02Proof.infimum_toReal_le_cost hd hε.le ht.1
  have hgapnon := V02Proof.infimum_toReal_le_cost hd hε.le (hmin.1 ν)
  have hlin := clockEnergyLinear_bound (hmin.1 ν) hΓ.1 (by linarith [hG j]) hΓD
  have hb := backward_quotient_estimate hs₀ (htime (hmin.1 ν))
    (add_nonneg (by norm_num) (mul_nonneg Real.pi_pos.le (hG0 j))) hε.le ENNReal.toReal_nonneg hR hρ
    hlin hgapnon hlower ht.2
  simpa only [C, gap] using hb

end Yau.Blueprint.V04Proof.ClockTaylorAux
