import Yau.Proofs.V04ClockNormalizerBounds

/-! The four wall powers cancel in the exact original weighted cost.
The remaining bound is chosen before every minimizing disc and delta. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem setup_center_time_lower {d : VariationData X q} (hd : VariationSetup d) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ {j : ℕ} {F : VariationDisc X},
      AdmissibleVariationDisc d j F → s₀ ≤ F.s := by
  have hc := hd.2.2.2.2.2.2.2.1
  obtain ⟨p, hp, hmin⟩ := hc.1.exists_isMinOn
    ⟨d.contact, interior_subset hc.2.1⟩ continuous_snd.continuousOn
  refine ⟨p.2, (hc.2.2.1 hp).2.1, fun {j F} hF => ?_⟩
  exact hmin ((hF.2.2.2.2.2.1).2)

theorem clockWeightRaw_le_wall_four {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    clockWeightRaw d k j a F θ ≤ wallPower d j a (F.f (circlePoint θ)) ^ 4 := by
  have hχ := ((hk.2.2.2.1 j).2.2.1 (F.f (circlePoint θ)).1).1
  have hψ := ((hk.2.2.2.1 j).2.2.2.2.1 (F.f (circlePoint θ))).1
  have hρ := setup_rho_nonneg hd (F.f (circlePoint θ)).1
    (admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).1.le
  have hj : 0 ≤ (k.dampingPower : ℝ) * Real.log (j + 3) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith))
  have hC := Real.log_nonneg (hk.2.2.2.1 j).1
  have hB : 0 ≤ (k.dampingPower : ℝ) * Real.log (1 + d.B j) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [(setup_index_bounds hd j).2]))
  have hb := mul_nonneg hχ (add_nonneg hρ hj)
  have hf := mul_nonneg hψ (add_nonneg (add_nonneg hC hj) hB)
  have heq := clockWeightRaw_neg_log (k := k) (a := a) hd hF θ
  have hlog : Real.log (clockWeightRaw d k j a F θ) ≤
      Real.log (wallPower d j a (F.f (circlePoint θ)) ^ 4) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [heq, hb, hf]
  exact (Real.log_le_log_iff (clockWeightRaw_pos hd hF θ)
    (pow_pos (admissible_wallPower_bounds hd hF a θ).1 4)).mp hlog

theorem clockWeight_inverse_wall_le {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    clockWeight d k j a F θ * (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ ≤
      (circleAverage (clockWeightRaw d k j a F))⁻¹ := by
  have hZ := clockWeightRaw_average_pos (a := a) hd hF (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hm := pow_pos (admissible_wallPower_bounds hd hF a θ).1 4
  have hr : clockWeightRaw d k j a F θ *
      (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ ≤ 1 :=
    (mul_inv_le_iff₀ hm).2 (by simpa only [one_mul] using clockWeightRaw_le_wall_four hd hk hF θ)
  change (clockWeightRaw d k j a F θ / circleAverage (clockWeightRaw d k j a F)) *
    (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ ≤ _
  rw [div_mul_eq_mul_div]
  exact (div_le_div_of_nonneg_right hr hZ.le).trans_eq (one_div _)

theorem fixed_index_clock_boundary_weight_bound {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ F : ℕ → VariationDisc X, MinimizingSequence d j ε F →
        ∀ᶠ ν in atTop, ∀ θ,
          0 ≤ discTime (F ν) (circlePoint θ) / (F ν).s * clockWeight d k j a (F ν) θ *
            (wallPower d j a ((F ν).f (circlePoint θ)) ^ 4)⁻¹ ∧
          discTime (F ν) (circlePoint θ) / (F ν).s * clockWeight d k j a (F ν) θ *
            (wallPower d j a ((F ν).f (circlePoint θ)) ^ 4)⁻¹ ≤ C := by
  obtain ⟨s₀, hs₀, htime⟩ := setup_center_time_lower hd
  obtain ⟨z, hz, hZ⟩ := fixed_index_clock_normalizer_lower hd hk j a
  refine ⟨(d.T / s₀) * z⁻¹, mul_nonneg (div_nonneg hd.1.le hs₀.le) (inv_nonneg.mpr hz.le),
    fun ε hε hε1 F hF => ?_⟩
  filter_upwards [hZ ε hε hε1 F hF] with ν hν θ
  have hA := hF.1 ν
  have ht := admissible_discTime_mem hA (circlePoint_mem_closedBall θ)
  have hs := hA.2.2.2.1
  have hnormal := clockWeightRaw_average_pos (a := a) hd hA (clockWeightRaw_contDiff (a := a) hd hk hA).continuous
  have hγ := (clockWeight_normalization (a := a) hd hA (clockWeightRaw_contDiff (a := a) hd hk hA).continuous).1 θ
  have hm := pow_pos (admissible_wallPower_bounds hd hA a θ).1 4
  have hrat : discTime (F ν) (circlePoint θ) / (F ν).s ≤ d.T / s₀ :=
    div_le_div₀ hd.1.le ht.2.le hs₀ (htime hA)
  have hweight := (clockWeight_inverse_wall_le (a := a) hd hk hA θ).trans
    (inv_anti₀ hz hν)
  constructor
  · exact mul_nonneg (mul_nonneg (div_nonneg ht.1.le hs.le) hγ.le) (inv_nonneg.mpr hm.le)
  · rw [mul_assoc]
    exact mul_le_mul hrat hweight (mul_nonneg hγ.le (inv_nonneg.mpr hm.le))
      (div_nonneg hd.1.le hs₀.le)

end Yau.Blueprint.V04Proof
