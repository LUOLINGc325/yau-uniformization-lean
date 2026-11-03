import Yau.Blueprint.Nodes

/-! The original square-root lower spacing supplies the eventual unit
spacing used by U01. No new grid or clock is introduced. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem unit_spacing_of_sqrt_spacing {s : ℕ → ℝ} {ch delta : ℝ}
    (hs : Tendsto s atTop atTop) (hch : 0 < ch)
    (hstep : ∀ᶠ k in atTop,
      ch * Real.sqrt (s k) ≤ s (k + 1) - s k ∧
      s (k + 1) - s k ≤ delta * s k) :
    ∀ᶠ k in atTop,
      1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + delta) * s k := by
  filter_upwards [hstep, (tendsto_atTop.1 hs) ((1 / ch) ^ 2)] with k hk hsk
  have hroot : 1 / ch ≤ Real.sqrt (s k) := by
    have hh := Real.sqrt_le_sqrt hsk
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / ch)] using hh
  have hunit : 1 ≤ ch * Real.sqrt (s k) := by
    have hh := mul_le_mul_of_nonneg_left hroot hch.le
    have hc : ch * (1 / ch) = 1 := by field_simp
    rw [hc] at hh
    exact hh
  exact ⟨hunit.trans hk.1, by linarith [hk.2]⟩

theorem models_unit_spacing {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {ρ : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv) :
    let s := fun k => ρ o (tk k)
    ∀ᶠ k in atTop,
      1 ≤ s (k + 1) - s k ∧ s (k + 1) ≤ (1 + (Real.exp hm - 1)) * s k := by
  obtain ⟨ch, hch, K, hK⟩ := hp.2.2.2.1
  exact unit_spacing_of_sqrt_spacing hp.2.1 hch (eventually_atTop.2 ⟨K, hK⟩)

end Yau.NodeProofs.U02Proof
