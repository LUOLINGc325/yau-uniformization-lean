import Yau.Proofs.Y03Frames

/-! Actual logarithmic clock increments bound each nonnegative singular rate. -/

open scoped Topology Matrix
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n}

theorem logarithmic_clock_slope_le {o : Pt X} {h : Flow X} {ρ : STF X}
    {t t' B : ℝ} (ht : 0 < t) (htt' : t < t')
    (hd : ∀ s ∈ Icc t t', HasDerivAt (ρ o) (scalarCurvature (h s) o) s)
    (hq : ∀ s ∈ Icc t t', clockSpeed o h s ≤ B) :
    (ρ o t' - ρ o t) / Real.log (t' / t) ≤ B := by
  let T := Real.log (t' / t)
  have hT : 0 < T := Real.log_pos ((one_lt_div ht).2 htt')
  have hend : t * Real.exp T = t' := by
    rw [Real.exp_log (div_pos (ht.trans htt') ht)]
    field_simp [ne_of_gt ht]
  have hmem (τ : ℝ) (hτ : τ ∈ Icc 0 T) : t * Real.exp τ ∈ Icc t t' := by
    constructor
    · have h := Real.exp_le_exp.2 hτ.1
      rw [Real.exp_zero] at h
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h ht.le
    · rw [← hend]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hτ.2) ht.le
  let u := fun τ => ρ o (t * Real.exp τ)
  let d := fun τ => clockSpeed o h (t * Real.exp τ)
  have hu (τ : ℝ) (hτ : τ ∈ Icc 0 T) : HasDerivAt u (d τ) τ := by
    convert (hd _ (hmem τ hτ)).comp τ ((Real.hasDerivAt_exp τ).const_mul t) using 1
    · rfl
    · unfold d clockSpeed; ring
  obtain ⟨c, hc, hder⟩ := exists_hasDerivAt_eq_slope u d hT
    (fun τ hτ => (hu τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => hu τ ⟨hτ.1.le, hτ.2.le⟩)
  have hb := hq _ (hmem c ⟨hc.1.le, hc.2.le⟩)
  change d c ≤ B at hb
  rw [hder] at hb
  simpa only [u, T, hend, Real.exp_zero, mul_one, sub_zero] using hb

theorem trace_rate_of_shrinkingCharts {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) : ∀ k, ∑ i, rate F tk E k i =
      (ρ o (tk (k + 1)) - ρ o (tk k)) / Real.log (tk (k + 1) / tk k) := by
  apply trace_rate_of_det (s := fun k => ρ o (tk k)) hE
  intro k
  rw [derivativeMatrix_det]
  exact (hCharts.2.2.2.2.2.1 (tk k) (tk (k + 1)) (hlate k) (hE k).2.1.le).2.2.2.2.2.1

theorem actual_rate_le_clock_bound {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) {B : ℝ}
    (hd : ∀ s ∈ Icc (tk k) (tk (k + 1)), HasDerivAt (ρ o) (scalarCurvature (h s) o) s)
    (hq : ∀ s ∈ Icc (tk k) (tk (k + 1)), clockSpeed o h s ≤ B) (i : Fin n) :
    rate F tk E k i ≤ B := by
  apply le_trans (Finset.single_le_sum (fun j _ => rate_nonneg hE k j) (Finset.mem_univ i))
  rw [trace_rate_of_shrinkingCharts hCharts hE hlate k]
  exact logarithmic_clock_slope_le (hE k).1 (hE k).2.1 hd hq

end Yau.Blueprint.Alignment.Y03Proof
