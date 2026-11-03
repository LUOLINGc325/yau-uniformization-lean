import Yau.Proofs.Y01PrimaryBounds
import Yau.Proofs.Y01PolynomialGrowth

/-! The polynomial center bounds of the same primary coordinates follow
from original aligned changes and the canonical macro-clock inequality. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

theorem aligned_plus_polynomial_bound
    {D : ℕ → Herm n} {w : ℕ → Fin n → ℝ} {S : ℕ → ℝ}
    {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm C c : ℝ} {L : Changes n}
    (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt D w (macroAt Q N M hm j₀) S C c L k) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      matOpNorm (L.plus k) + matOpNorm (L.plus k)⁻¹ ≤
        (1 + gridClock Q N M hm j₀ k) ^ Cp := by
  obtain ⟨p, hp, hbound⟩ := affine_real_power_bound (inv_nonneg.2 hhm.le) C
  refine ⟨p, hp, ?_⟩
  intro k hk
  apply (hL k hk).2.2.2.2.1.trans
  apply hbound _ _ (gridClock_one_le hhm.le hgrid k) (Nat.cast_nonneg _)
  simpa only [div_eq_mul_inv, mul_comm] using macroAt_le_clock_div hhm k

theorem primaryDerivative_polynomial_bounds
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps : ℝ}
    (hhm : 0 < hm) (hgrid : GridLayout Q N M hm j₀) {L : Changes n} {C c : ℝ}
    (hc : 0 < c)
    (hL : ∀ k, Regular Q N M (macroAt Q N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
        (macroAt Q N M hm j₀) (macroClock hm) C c L k) :
    ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ k,
      matOpNorm (primaryDerivative (fun k => Regular Q N M (macroAt Q N M hm j₀ k)) E L k) +
        matOpNorm (primaryDerivative (fun k => Regular Q N M (macroAt Q N M hm j₀ k)) E L k)⁻¹ ≤
          (1 + gridClock Q N M hm j₀ k) ^ Cp := by
  let s := gridClock Q N M hm j₀
  let j := macroAt Q N M hm j₀
  have hs k : 1 ≤ s k := gridClock_one_le hhm.le hgrid k
  obtain ⟨p, hp, hmacroPower⟩ := affine_real_power_bound (inv_nonneg.2 hhm.le) C
  have hjPower k : (1 + (j k : ℝ)) ^ C ≤ (1 + s k) ^ p := by
    apply hmacroPower (s k) (j k) (hs k) (Nat.cast_nonneg _)
    simpa only [div_eq_mul_inv, mul_comm] using macroAt_le_clock_div hhm k
  let r := (n + 1 : ℝ) / Real.log 2 + (1 + max p (2 / Real.log 2)) * (n + 1 : ℝ)
  let Cp := max 1 (max p r)
  have hCp : 1 ≤ Cp := le_max_left _ _
  have hpCp : p ≤ Cp := (le_max_left _ _).trans (le_max_right _ _)
  have hrCp : r ≤ Cp := (le_max_right _ _).trans (le_max_right _ _)
  have hCp0 : 0 ≤ Cp := zero_le_one.trans hCp
  have hminus k (hk : Regular Q N M (j k)) :
      matOpNorm (L.minus k) + matOpNorm (L.minus k)⁻¹ ≤ (1 + s k) ^ Cp := by
    have hraw := minus_change_polynomial_bound hE hc (hL k hk)
    have hsum := polynomial_sum_bound (hs k) (hjPower k)
      (constant_le_real_power (by norm_num : (0 : ℝ) ≤ 2) (hs k))
    have hpow := polynomial_nat_power_bound (hs k)
      (by positivity : (0 : ℝ) ≤ (1 + (j k : ℝ)) ^ C + 2) hsum (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hpow
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ n + 1)
    have habsorb := constant_mul_real_power (p := (1 + max p (2 / Real.log 2)) * (n + 1 : ℝ))
      (by positivity : (0 : ℝ) ≤ n + 1) (hs k)
    exact hraw.trans (hmul.trans (habsorb.trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hs k]) hrCp)))
  have hplus k (hk : Regular Q N M (j k)) :
      matOpNorm (L.plus k) + matOpNorm (L.plus k)⁻¹ ≤ (1 + s k) ^ Cp :=
    (hL k hk).2.2.2.2.1.trans ((hjPower k).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hs k]) hpCp))
  refine ⟨Cp, hCp, ?_⟩
  apply primary_change_norm_bound hE
  · intro a b hab
    exact Real.rpow_le_rpow (by linarith [hs a])
      (by linarith [hgrid.2.1.monotone hab]) hCp0
  · intro k
    have hbase : (2 : ℝ) ≤ 1 + s k := by linarith [hs k]
    have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith [hs k] : 1 ≤ 1 + s k) hCp
    exact hbase.trans (by simpa only [Real.rpow_one] using hpow)
  · exact hminus
  · exact hplus

end Yau.Proofs.Y01Aux
