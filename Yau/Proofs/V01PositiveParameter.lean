import spec.CHAIN.CONTRACTS

/-! Small positive spectral parameters are selected after the localization
index and its replacement constant have been fixed. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Yau.Blueprint.V01Proof

theorem eventually_positive_small_product (D b : ℝ) (hb : 0 < b) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ 1 ∧ D * δ ≤ b := by
  have hProd : Tendsto (fun δ : ℝ => D * δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun δ : ℝ => D * δ) 0 := by fun_prop
    simpa only [mul_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1),
    hProd.eventually (Iio_mem_nhds hb)] with δ hδ hD
  exact ⟨hδ.1, hδ.2.le, hD.le⟩

theorem nonneg_coefficient_small_of_abs {C x b : ℝ}
    (hC : 0 ≤ C) (hx : |x| ≤ b / (C + 1)) : C * x ≤ b := by
  have hDen : 0 < C + 1 := by linarith
  have hb := (le_div_iff₀ hDen).mp hx
  calc
    C * x ≤ C * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hC
    _ ≤ |x| * (C + 1) := by nlinarith [abs_nonneg x]
    _ ≤ b := hb

end Yau.Blueprint.V01Proof
