import Yau.Proofs.V04ClockTaylorCalculus

/-! Sign and denominator bookkeeping for a fixed negative increment. -/
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux

theorem backward_quotient_estimate {s₀ s K ε e A b R ρ J₀ J₁ μ : ℝ}
    (hs₀ : 0 < s₀) (hss : s₀ ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε) (he : 0 ≤ e)
    (hR : 0 ≤ R) (hρ : 0 < ρ) (hlinear : |A| ≤ K * e)
    (hμ₀ : μ ≤ J₀) (hμ₁ : μ ≤ J₁)
    (hTaylor : |J₁ - J₀ - (-ρ) * (s * b + ε * A)| ≤ R * (-ρ) ^ 2) :
    b - (K / s₀) * ε * (1 + e) ≤ ((J₀ - μ) / s₀) / ρ + (R / s₀) * ρ := by
  have hs : 0 < s := hs₀.trans_le hss
  have hKs : K ≤ s * (K / s₀) := by
    calc
      K = s₀ * (K / s₀) := by field_simp
      _ ≤ s * (K / s₀) := mul_le_mul_of_nonneg_right hss (div_nonneg hK hs₀.le)
  have hCorr : K * e ≤ s * (K / s₀) * (1 + e) :=
    (mul_le_mul_of_nonneg_right hKs he).trans
      (mul_le_mul_of_nonneg_left (by linarith : e ≤ 1 + e)
        (mul_nonneg hs.le (div_nonneg hK hs₀.le)))
  have hA := mul_le_mul_of_nonneg_left (abs_le.mp hlinear).1 hε
  have hC := mul_le_mul_of_nonneg_left hCorr hε
  have hlow : s * (b - (K / s₀) * ε * (1 + e)) ≤ s * b + ε * A := by nlinarith
  have ht := (abs_le.mp hTaylor).2
  have hq : s * b + ε * A ≤ (J₀ - μ) / ρ + R * ρ := by
    apply (mul_le_mul_iff_left₀ hρ).mp
    have hmain : ρ * (s * b + ε * A) ≤ J₀ - μ + R * ρ ^ 2 := by nlinarith
    have hid : ((J₀ - μ) / ρ + R * ρ) * ρ = J₀ - μ + R * ρ ^ 2 := by field_simp
    rw [hid]
    nlinarith
  have hnon : 0 ≤ (J₀ - μ) / ρ + R * ρ :=
    add_nonneg (div_nonneg (sub_nonneg.mpr hμ₀) hρ.le) (mul_nonneg hR hρ.le)
  calc
    _ ≤ (s * b + ε * A) / s := (le_div_iff₀ hs).mpr (by nlinarith)
    _ ≤ ((J₀ - μ) / ρ + R * ρ) / s := div_le_div_of_nonneg_right hq hs.le
    _ ≤ ((J₀ - μ) / ρ + R * ρ) / s₀ := div_le_div_of_nonneg_left hnon hs₀ hss
    _ = _ := by field_simp

end Yau.Blueprint.V04Proof.ClockTaylorAux
