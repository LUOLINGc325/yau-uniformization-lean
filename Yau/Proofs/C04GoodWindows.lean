import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Selection of arbitrarily late multiplicative good windows. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.C04Aux

/-- Failure of every late good window forces quadratic growth, contradicting
the low linear-growth points. The function here is indexed by volume clock. -/
theorem exists_multiplicative_good_window {q : ℝ → ℝ} {A L K : ℝ}
    (hA : 0 < A) (hL : 1 < L) (hK : L ^ 2 < K)
    (hq : MonotoneOn q (Ici A)) (hqA : 0 < q A)
    (hlow : ∀ T, ∃ t, T ≤ t ∧ q t ≤ 3 * t) :
    ∀ T, ∃ t, T ≤ t ∧ A ≤ t ∧ q (L * t) ≤ K * q t := by
  intro T
  by_contra hn
  push_neg at hn
  let B := max A T
  have hAB : A ≤ B := le_max_left _ _
  have hTB : T ≤ B := le_max_right _ _
  have hB : 0 < B := hA.trans_le hAB
  have hqB : 0 < q B := hqA.trans_le (hq (le_refl A) hAB hAB)
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hpow : ∀ k : ℕ, B ≤ L ^ k * B := by
    intro k
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ hL.le) hB.le
  have hind : ∀ k : ℕ, (L ^ k) ^ 2 * q B ≤ q (L ^ k * B) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxA : A ≤ L ^ k * B := hAB.trans (hpow k)
      have hxT : T ≤ L ^ k * B := hTB.trans (hpow k)
      have hxq : 0 < q (L ^ k * B) :=
        hqB.trans_le (hq hAB hxA (hpow k))
      have hstep := hn (L ^ k * B) hxT hxA
      calc
        (L ^ (k + 1)) ^ 2 * q B = L ^ 2 * ((L ^ k) ^ 2 * q B) := by
          rw [pow_succ]
          ring
        _ ≤ L ^ 2 * q (L ^ k * B) := mul_le_mul_of_nonneg_left ih (sq_nonneg L)
        _ ≤ K * q (L ^ k * B) := mul_le_mul_of_nonneg_right hK.le hxq.le
        _ ≤ q (L ^ (k + 1) * B) := by
          convert hstep.le using 1 <;> simp only [pow_succ] <;> ring
  let D := 3 * L ^ 2 * B ^ 2 / q B + 1
  obtain ⟨t, ht, hqt⟩ := hlow (max B D)
  have htB : B ≤ t := (le_max_left _ _).trans ht
  have htD : D ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := hB.trans_le htB
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near ((one_le_div hB).mpr htB) hL
  have hlo : L ^ k * B ≤ t := (le_div_iff₀ hB).mp hklo
  have hhi : t < L * (L ^ k * B) := by
    have hh := (div_lt_iff₀ hB).mp hkhi
    simpa only [pow_succ, mul_assoc, mul_comm L, mul_left_comm L] using hh
  have hp0 : 0 ≤ L ^ k := (pow_pos hL0 k).le
  have hsquare : t ^ 2 ≤ L ^ 2 * (L ^ k) ^ 2 * B ^ 2 := by
    calc
      t ^ 2 ≤ (L * (L ^ k * B)) ^ 2 :=
        (sq_le_sq₀ ht0.le (by positivity)).mpr hhi.le
      _ = L ^ 2 * (L ^ k) ^ 2 * B ^ 2 := by ring
  have hqlo : (L ^ k) ^ 2 * q B ≤ q t :=
    (hind k).trans (hq (hAB.trans (hpow k)) (hAB.trans htB) hlo)
  have hquad : q B * t ^ 2 ≤ L ^ 2 * B ^ 2 * q t := calc
    q B * t ^ 2 ≤ q B * (L ^ 2 * (L ^ k) ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left hsquare hqB.le
    _ = (L ^ 2 * B ^ 2) * ((L ^ k) ^ 2 * q B) := by ring
    _ ≤ (L ^ 2 * B ^ 2) * q t := mul_le_mul_of_nonneg_left hqlo (by positivity)
  have hup : L ^ 2 * B ^ 2 * q t ≤ (3 * L ^ 2 * B ^ 2) * t := by
    have hh := mul_le_mul_of_nonneg_left hqt (show 0 ≤ L ^ 2 * B ^ 2 by positivity)
    nlinarith
  have hstrict : 3 * L ^ 2 * B ^ 2 < q B * t := by
    have hh := mul_le_mul_of_nonneg_left htD hqB.le
    dsimp [D] at hh
    rw [mul_add, mul_div_cancel₀ _ hqB.ne', mul_one] at hh
    linarith
  nlinarith

end Yau.Proofs.C04Aux
