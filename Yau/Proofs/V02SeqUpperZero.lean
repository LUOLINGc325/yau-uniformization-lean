import Yau.Blueprint.VariationContracts

/-! The three successive limits used to test an infimum. The radius is
chosen after the auxiliary loss and before taking the sequence limit. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V02Proof

/-- A loss-dependent radius never enters the coefficient of a separate
penalty. This is a statement about real sequences, with no geometric input. -/
theorem seqUpperZero_of_three_limits {a gap : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hgap : Tendsto gap atTop (𝓝 0))
    (hbound : ∀ η : ℝ, 0 < η → ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r → ∀ ν,
        a ν ≤ gap ν / ρ ^ 2 + C * ρ + M * η) :
    SeqUpperZero a := by
  intro τ hτ
  let η : ℝ := τ / (3 * (M + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : 3 * (M + 1) * η = τ := by
    dsimp [η]
    field_simp
  have hMη : M * η ≤ τ / 3 := by nlinarith
  obtain ⟨r, C, hr, hC, hb⟩ := hbound η hη
  let ρ : ℝ := min (r / 2) (τ / (6 * (C + 1)))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r :=
    (min_le_left _ _).trans_lt (half_lt_self hr)
  have hρsmall : 6 * (C + 1) * ρ ≤ τ := by
    have h := min_le_right (r / 2) (τ / (6 * (C + 1)))
    simpa only [ρ, mul_comm] using
      (le_div_iff₀ (by positivity : 0 < 6 * (C + 1))).mp h
  have hCρ : C * ρ ≤ τ / 3 := by nlinarith
  have hlate := hgap.eventually (Iio_mem_nhds
    (by positivity : (0 : ℝ) < ρ ^ 2 * (τ / 3)))
  filter_upwards [hlate] with ν hν
  have hgapν : gap ν / ρ ^ 2 ≤ τ / 3 :=
    (div_le_iff₀ (sq_pos_of_pos hρ)).mpr (by nlinarith [hν])
  have ha := hb ρ hρ hρr ν
  linarith

/-- The estimate obtained by dividing the actual cubic Taylor remainder
by a fixed positive radius squared. -/
theorem negative_mixed_le_gap_of_taylor {μ J₀ avg mixed C ρ : ℝ}
    (hρ : 0 < ρ) (hlower : μ ≤ avg)
    (hTaylor : |avg - J₀ - ρ ^ 2 * mixed| ≤ C * ρ ^ 3) :
    -mixed ≤ (J₀ - μ) / ρ ^ 2 + C * ρ := by
  have ht := (abs_le.mp hTaylor).2
  have heq : ((J₀ - μ) / ρ ^ 2 + C * ρ) * ρ ^ 2 =
      J₀ - μ + C * ρ ^ 3 := by
    field_simp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hρ)).mp
  rw [heq]
  nlinarith

end Yau.Blueprint.V02Proof
