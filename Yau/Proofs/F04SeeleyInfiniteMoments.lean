import Yau.Proofs.F04SeeleyDecay

open Filter
open scoped Topology

noncomputable section

namespace Yau.F04Proof.Seeley

def majorantMoment (m k : ℕ) : ℝ := weightMajorant k * dyadic k ^ m

theorem majorantMoment_nonneg (m k : ℕ) : 0 ≤ majorantMoment m k :=
  mul_nonneg (weightMajorant_nonneg k) (pow_nonneg (dyadic_pos k).le _)

theorem majorantMoment_succ (m k : ℕ) :
    majorantMoment m (k + 1) = majorantMoment m k * (dyadic (m + 1) / dyadic k) := by
  unfold majorantMoment weightMajorant
  rw [triangular_succ, dyadic_add]
  simp only [dyadic, pow_succ, mul_pow]
  field_simp
  ring

theorem majorantMoment_summable (m : ℕ) : Summable (majorantMoment m) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [eventually_ge_atTop (m + 2)] with k hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (majorantMoment_nonneg m (k + 1)),
    abs_of_nonneg (majorantMoment_nonneg m k), majorantMoment_succ]
  have hB : dyadic (m + 2) ≤ dyadic k := dyadic_strictMono.monotone hk
  have hdouble : 2 * dyadic (m + 1) ≤ dyadic k := by
    convert hB using 1
    simp only [dyadic, pow_succ]
    ring
  have hratio : dyadic (m + 1) / dyadic k ≤ 1 / 2 := by
    apply (div_le_iff₀ (dyadic_pos k)).mpr
    linarith
  nlinarith [mul_nonneg (majorantMoment_nonneg m k) (sub_nonneg.mpr hratio)]

theorem seeleyWeight_summable (m : ℕ) :
    Summable (fun k => |seeleyWeight k| * dyadic k ^ m) := by
  apply (majorantMoment_summable m).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
    (pow_nonneg (dyadic_pos k).le _))]
  exact mul_le_mul_of_nonneg_right (seeleyWeight_abs_le k) (pow_nonneg (dyadic_pos k).le _)

theorem seeleyWeight_signed_moment_summable (m : ℕ) :
    Summable (fun k => seeleyWeight k * (-dyadic k) ^ m) := by
  apply (majorantMoment_summable m).of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (dyadic_pos k)]
  exact mul_le_mul_of_nonneg_right (seeleyWeight_abs_le k) (pow_nonneg (dyadic_pos k).le _)

theorem finiteWeight_tsum (N m : ℕ) :
    (∑' k, finiteWeight N k * (-dyadic k) ^ m) =
      ∑ k ∈ Finset.range (N + 1), finiteWeight N k * (-dyadic k) ^ m := by
  apply tsum_eq_sum
  intro k hk
  have hNk : N < k := by
    simp only [Finset.mem_range] at hk
    omega
  rw [finiteWeight_eq_zero_of_lt N k hNk, zero_mul]

theorem seeleyWeight_moment (m : ℕ) :
    HasSum (fun k => seeleyWeight k * (-dyadic k) ^ m) 1 := by
  have hlim : Tendsto (fun N => ∑' k, finiteWeight N k * (-dyadic k) ^ m)
      atTop (𝓝 (∑' k, seeleyWeight k * (-dyadic k) ^ m)) := by
    apply tendsto_tsum_of_dominated_convergence (majorantMoment_summable m)
    · intro k
      exact (finiteWeight_tendsto k).mul_const _
    · apply Eventually.of_forall
      intro N k
      simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (dyadic_pos k)]
      exact mul_le_mul_of_nonneg_right (finiteWeight_abs_le N k)
        (pow_nonneg (dyadic_pos k).le _)
  have hone : Tendsto (fun N => ∑' k, finiteWeight N k * (-dyadic k) ^ m)
      atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m] with N hN
    exact (finiteWeight_tsum N m).trans (finiteWeight_moment N m hN) |>.symm
  have heq := tendsto_nhds_unique hlim hone
  rw [← heq]
  exact (seeleyWeight_signed_moment_summable m).hasSum

end Yau.F04Proof.Seeley
