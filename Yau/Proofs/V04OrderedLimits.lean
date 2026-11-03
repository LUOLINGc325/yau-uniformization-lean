import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! The sequence index is eliminated before the positive parameter tends to
zero. The frequency chosen below depends only on that parameter. -/

open Filter
open scoped Topology

noncomputable section
namespace Yau.Blueprint.V04Proof

private def tailUpperBounds (x : ℕ → ℝ) : Set ℝ :=
  {b | ∀ᶠ ν in atTop, x ν ≤ b}

private theorem tailUpperBounds_bddBelow {x : ℕ → ℝ} (hx : ∀ ν, 1 ≤ x ν) :
    BddBelow (tailUpperBounds x) := by
  refine ⟨1, fun b hb => ?_⟩
  obtain ⟨ν, hν⟩ := hb.exists
  exact (hx ν).trans hν

/-- A cap chosen before the sequence index, with vanishing penalized size.
The unbounded branch has no use of a conditionally complete infimum. -/
theorem exists_ordered_energy_cap (x : ℝ → ℕ → ℝ)
    (hx : ∀ ε ν, 1 ≤ x ε ν)
    (hzero : ∀ r, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ᶠ ν in atTop, |ε * x ε ν| ≤ r) :
    ∃ B : ℝ → ℝ, (∀ ε, 1 ≤ B ε) ∧
      Tendsto (fun ε => ε * B ε) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop, x ε ν ≤ B ε) := by
  classical
  let B : ℝ → ℝ := fun ε =>
    if (tailUpperBounds (x ε)).Nonempty then 2 * sInf (tailUpperBounds (x ε)) else 1
  have hinf : ∀ ε, (tailUpperBounds (x ε)).Nonempty →
      1 ≤ sInf (tailUpperBounds (x ε)) := by
    intro ε hε
    exact le_csInf hε fun b hb => by
      obtain ⟨ν, hν⟩ := hb.exists
      exact (hx ε ν).trans hν
  have hB : ∀ ε, 1 ≤ B ε := by
    intro ε
    dsimp [B]
    split_ifs with hε
    · have := hinf ε hε
      linarith
    · exact le_rfl
  have hbounded : ∀ ε, 0 < ε → ∀ r, 0 < r →
      (∀ᶠ ν in atTop, |ε * x ε ν| ≤ r) →
      (tailUpperBounds (x ε)).Nonempty ∧ ε * B ε ≤ 2 * r := by
    intro ε hε r hr htail
    have hmem : r / ε ∈ tailUpperBounds (x ε) := by
      filter_upwards [htail] with ν hν
      apply (le_div_iff₀ hε).2
      simpa only [mul_comm] using (le_abs_self (ε * x ε ν)).trans hν
    have hnon : (tailUpperBounds (x ε)).Nonempty := ⟨_, hmem⟩
    refine ⟨hnon, ?_⟩
    have hi := csInf_le (tailUpperBounds_bddBelow (hx ε)) hmem
    have hi' : ε * sInf (tailUpperBounds (x ε)) ≤ r := by
      simpa only [mul_comm] using (le_div_iff₀ hε).1 hi
    dsimp [B]
    simp only [hnon, ite_true]
    nlinarith
  refine ⟨B, hB, ?_, ?_⟩
  · apply Metric.tendsto_nhds.2
    intro r hr
    filter_upwards [hzero (r / 4) (by positivity), self_mem_nhdsWithin]
      with ε htail hε
    have hbound := (hbounded ε hε (r / 4) (by positivity) htail).2
    have hnonneg : 0 ≤ ε * B ε := mul_nonneg hε.le (by linarith [hB ε])
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
      (show ε * B ε < r by linarith)
  · filter_upwards [hzero 1 zero_lt_one, self_mem_nhdsWithin] with ε htail hε
    have hnon := (hbounded ε hε 1 zero_lt_one htail).1
    obtain ⟨b, hb, hblt⟩ := exists_lt_of_csInf_lt hnon
      (show sInf (tailUpperBounds (x ε)) < sInf (tailUpperBounds (x ε)) + 1 by linarith)
    have hi := hinf ε hnon
    filter_upwards [hb] with ν hν
    dsimp [B]
    simp only [hnon, ite_true]
    linarith

/-- The exact upward-rounded frequency appearing in the frozen contract. -/
theorem intermediate_frequency_limits (B : ℝ → ℝ) (hB : ∀ ε, 1 ≤ B ε)
    (hzero : Tendsto (fun ε => ε * B ε) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε => B ε / (max 1 (Nat.ceil (Real.sqrt (B ε / ε))) : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun ε => ε * (max 1 (Nat.ceil (Real.sqrt (B ε / ε))) : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let P : ℝ → ℕ := fun ε => max 1 (Nat.ceil (Real.sqrt (B ε / ε)))
  have hP : ∀ ε, 0 < ε →
      0 ≤ B ε / (P ε : ℝ) ∧
      B ε / (P ε : ℝ) ≤ Real.sqrt (ε * B ε) ∧
      0 ≤ ε * (P ε : ℝ) ∧
      ε * (P ε : ℝ) ≤ Real.sqrt (ε * B ε) + ε := by
    intro ε hε
    have hb : 0 < B ε := lt_of_lt_of_le zero_lt_one (hB ε)
    have hp : (0 : ℝ) < P ε := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    have hu : 0 ≤ Real.sqrt (B ε / ε) := Real.sqrt_nonneg _
    have husq : Real.sqrt (B ε / ε) ^ 2 = B ε / ε :=
      Real.sq_sqrt (div_nonneg hb.le hε.le)
    have hv : 0 ≤ Real.sqrt (ε * B ε) := Real.sqrt_nonneg _
    have hvsq : Real.sqrt (ε * B ε) ^ 2 = ε * B ε :=
      Real.sq_sqrt (mul_nonneg hε.le hb.le)
    have hp_lower : Real.sqrt (B ε / ε) ≤ (P ε : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 _))
    have hp_upper : (P ε : ℝ) ≤ Real.sqrt (B ε / ε) + 1 := by
      dsimp [P]
      rw [Nat.cast_max, Nat.cast_one]
      exact max_le (by linarith) (Nat.ceil_lt_add_one hu).le
    have hid : ε * Real.sqrt (B ε / ε) = Real.sqrt (ε * B ε) := by
      have hm : ε * Real.sqrt (B ε / ε) ^ 2 = B ε := by
        simpa only [mul_comm] using (eq_div_iff hε.ne').1 husq
      have hprod : 0 ≤ ε * Real.sqrt (B ε / ε) := mul_nonneg hε.le hu
      nlinarith [sq_nonneg (ε * Real.sqrt (B ε / ε) - Real.sqrt (ε * B ε))]
    refine ⟨div_nonneg hb.le hp.le, (div_le_iff₀ hp).2 ?_,
      mul_nonneg hε.le hp.le, ?_⟩
    · have hm : ε * Real.sqrt (B ε / ε) ^ 2 = B ε := by
        simpa only [mul_comm] using (eq_div_iff hε.ne').1 husq
      rw [← hid]
      have := mul_le_mul_of_nonneg_left hp_lower (mul_nonneg hε.le hu)
      nlinarith
    · have := mul_le_mul_of_nonneg_left hp_upper hε.le
      nlinarith [hid]
  have hsqrt : Tendsto (fun ε => Real.sqrt (ε * B ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hzero.sqrt
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  constructor
  · apply squeeze_zero' _ _ hsqrt
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hP ε hε).1
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hP ε hε).2.1
  · apply squeeze_zero' _ _ (by simpa using hsqrt.add heps)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hP ε hε).2.2.1
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hP ε hε).2.2.2

/-- The difference quotient is held fixed while the sequence limit is
taken. Only afterwards is its positive magnitude allowed to decrease. -/
theorem upper_zero_of_backward_quotients (a gap : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hgap : Tendsto gap atTop (𝓝 0))
    (hbound : ∀ h : ℝ, 0 < h → h < R →
      ∀ᶠ ν in atTop, a ν ≤ gap ν / h + C * h) :
    ∀ r : ℝ, 0 < r → ∀ᶠ ν in atTop, a ν ≤ r := by
  intro r hr
  let h := min (R / 2) (r / (2 * (C + 1)))
  have hh : 0 < h := lt_min (half_pos hR) (by positivity)
  have hhR : h < R := (min_le_left _ _).trans_lt (by linarith)
  have hhsmall : C * h ≤ r / 2 := by
    have hc1 : 0 < C + 1 := by linarith
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).1
      (min_le_right (R / 2) (r / (2 * (C + 1))))
    change h * (2 * (C + 1)) ≤ r at hm
    nlinarith
  have hlim : Tendsto (fun ν => gap ν / h) atTop (𝓝 0) := by
    simpa using hgap.div_const h
  filter_upwards [hbound h hh hhR, hlim.eventually (Iio_mem_nhds (half_pos hr))]
    with ν hν hsmall
  linarith

end Yau.Blueprint.V04Proof
