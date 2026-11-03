import Yau.Proofs.F04SeeleyProducts

open Filter
open scoped Topology

noncomputable section

namespace Yau.F04Proof.Seeley

theorem tail_factor_estimate (B C : ℝ) (hB : 1 ≤ B) (hC : 2 ≤ C) :
    (1 + B * C) / (B * C - B) ≤ ((1 - C⁻¹)⁻¹) ^ 2 := by
  have hCm : 0 < C - 1 := by linarith
  have hCn : C ≠ 0 := by linarith
  have hden : 0 < B * C - B := by nlinarith
  have heq0 : 1 - C⁻¹ = (C - 1) / C := by field_simp
  have heq : ((1 - C⁻¹)⁻¹) ^ 2 = C ^ 2 / (C - 1) ^ 2 := by
    rw [heq0, inv_div, div_pow]
  rw [heq, div_le_div_iff₀ hden (sq_pos_of_pos hCm)]
  have hbase : (1 + B * C) * (C - 1) ≤ B * C ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hbase hCm.le
  nlinarith

theorem reciprocal_dyadic (l : ℕ) : (1 / 2 : ℝ) ^ l = (dyadic l)⁻¹ := by
  simp [dyadic]

theorem tailFactor_le (k l : ℕ) :
    tailFactor k l ≤ ((1 - (1 / 2 : ℝ) ^ (l + 1))⁻¹) ^ 2 := by
  have hC : 2 ≤ dyadic (l + 1) := by
    simpa only [pow_one, dyadic] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ l + 1 by omega)
  rw [tailFactor, Nat.add_assoc, dyadic_add, reciprocal_dyadic]
  exact tail_factor_estimate (dyadic k) (dyadic (l + 1)) (dyadic_ge_one k) hC

theorem tailWeight_le_sixteen (k r : ℕ) : tailWeight k r ≤ 16 := by
  have hD := denominatorProduct_lower r
  have hDpos := denominatorProduct_pos r
  have hInv : (denominatorProduct r)⁻¹ ≤ 4 := by
    rw [← one_div]
    apply (div_le_iff₀ hDpos).mpr
    linarith
  calc
    tailWeight k r ≤ ∏ l ∈ Finset.range r,
        ((1 - (1 / 2 : ℝ) ^ (l + 1))⁻¹) ^ 2 :=
      Finset.prod_le_prod₀ (fun l _ => (tailFactor_ge_one k l).trans' zero_le_one)
        (fun l _ => tailFactor_le k l)
    _ = ((denominatorProduct r)⁻¹) ^ 2 := by
      simp only [denominatorProduct, Finset.prod_pow, Finset.prod_inv_distrib]
    _ ≤ 16 := by nlinarith [inv_nonneg.mpr hDpos.le]

def tailLimit (k : ℕ) : ℝ := ⨆ r, tailWeight k r

theorem tailLimit_bounds (k : ℕ) : 1 ≤ tailLimit k ∧ tailLimit k ≤ 16 := by
  have hb : BddAbove (Set.range (tailWeight k)) :=
    ⟨16, fun _ hx => by obtain ⟨r, rfl⟩ := hx; exact tailWeight_le_sixteen k r⟩
  constructor
  · have he : tailWeight k 0 ≤ tailLimit k := le_ciSup hb 0
    have he0 : tailWeight k 0 = 1 := by simp [tailWeight]
    rwa [he0] at he
  · exact ciSup_le (fun r => tailWeight_le_sixteen k r)

theorem tailWeight_tendsto (k : ℕ) :
    Tendsto (tailWeight k) atTop (𝓝 (tailLimit k)) := by
  exact tendsto_atTop_ciSup (tailWeight_mono k)
    ⟨16, fun _ hx => by obtain ⟨r, rfl⟩ := hx; exact tailWeight_le_sixteen k r⟩

end Yau.F04Proof.Seeley
