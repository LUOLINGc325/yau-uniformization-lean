import Yau.Proofs.F04SubcaloricEstimate
import Yau.Proofs.F04CompactMassLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem dominated_subcaloric_unique_with_cutoff (hG02 : G02) {n : ℕ}
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T C β : ℝ} {k : ℕ} (hT : 0 < T) (hC : 0 < C) (hβ : 0 < β) (hk : 2 * n ≤ k)
    {χ z : STF X} (hχ : SmoothSpaceC1Time χ (Icc 0 T)) (hz : SmoothSpaceTime z (Icc 0 T))
    (hdata : ∀ x t, t ∈ Icc 0 T →
      0 < χ x t ∧ χ x t ≤ C * (u x) ^ (-(k : ℤ)) ∧
      gradNormSq X.metric.form (fun y => χ y t) x ≤ (C * χ x t / u x) ^ 2 ∧
      HermLE (levi (fun y => χ y t) x) (((C * χ x t : ℝ) : ℂ) • gMat (h t) x) ∧
      (0 < t → deriv (χ x) t ≤ C * (1 + t ^ (β - 1)) * χ x t))
    (hzbound : ∀ x t, t ∈ Icc 0 T → 0 ≤ z x t ∧ z x t ≤ ρ x t)
    (hcal : ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) z x t ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → z x t = 0 := by
  obtain ⟨E, _, hfinite⟩ := finite_subcaloric_mass_estimate hG02 X o h U P ρ hloc u hu μ hμ
    hT hC hβ hk hχ hz hdata hzbound hcal
  have hden : SmoothSpaceTime (density ρ) (Icc 0 T) := (massVolumeTransport o h U P ρ hloc T hT).1
  intro x t ht
  let f : Pt X → ℝ := fun y => z y t * χ y t * density ρ y t
  have hfc : Continuous f :=
    (((LeafProofs.L18Aux.continuous_of_smoothFn ((smoothSpaceTime_c1 hz).1 t ht)).mul
      (LeafProofs.L18Aux.continuous_of_smoothFn (hχ.1 t ht))).mul
      (LeafProofs.L18Aux.continuous_of_smoothFn ((smoothSpaceTime_c1 hden).1 t ht)))
  have hf0 (y : Pt X) : 0 ≤ f y :=
    mul_nonneg (mul_nonneg (hzbound y t ht).1 (hdata y t ht).1.le) (density_pos ρ y t).le
  have hzero : ∀ N : ℕ, (∫ y, massCutoff u ((N : ℝ) + 1) y * f y ∂μ) = 0 := by
    apply monotone_mass_eq_zero_of_error_tendsto
      (E * t * Real.exp ((((n : ℝ) + 1) * C) * (t + t ^ β / β)))
      (compact_mass_monotone X o u hu μ hμ hfc hf0)
      (fun N => integral_nonneg (fun y => mul_nonneg (massCutoff_range u ((N : ℝ) + 1) y).1 (hf0 y)))
      (e := fun N : ℕ => ((N : ℝ) + 1) ^ (-(1 : ℝ)))
    · intro N
      calc
        _ ≤ (E / ((N : ℝ) + 1)) * t * Real.exp ((((n : ℝ) + 1) * C) * (t + t ^ β / β)) :=
          hfinite ((N : ℝ) + 1) (by have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith) t ht
        _ = (E * t * Real.exp ((((n : ℝ) + 1) * C) * (t + t ^ β / β))) *
            ((N : ℝ) + 1) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]; ring
    · exact cutoff_error_tendsto_zero (show (0 : ℝ) < 1 by norm_num)
  have hfx := compact_masses_zero_implies_zero X o u hu μ hμ hfc hf0 hzero x
  have he : z x t * (χ x t * density ρ x t) = 0 := by simpa only [f, mul_assoc] using hfx
  exact (mul_eq_zero.mp he).resolve_right
    (mul_ne_zero (hdata x t ht).1.ne' (density_pos ρ x t).ne')

/-- The exact registered dependencies produce the exhaustion, volume and
integrable cutoff used above, all for the originally supplied localized flow. -/
theorem dominated_subcaloric_uniqueness_from_dependencies (hP07 : P07) (hF03 : F03) (hG02 : G02)
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) {z : STF X}
    (hz : SmoothSpaceTime z (Icc 0 T))
    (hzbound : ∀ x t, t ∈ Icc 0 T → 0 ≤ z x t ∧ z x t ≤ ρ x t)
    (hcal : ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) z x t ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → z x t = 0 := by
  obtain ⟨u, hu⟩ := hP07 n X o
  obtain ⟨μ, hμ, _⟩ := hG02 n X.manifold X.metric.form
    (LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  obtain ⟨β, hβ, k₀, hcut⟩ := hF03 n X o h U P ρ hloc u hu T hT
  let k := max k₀ (2 * n)
  obtain ⟨χ, C, hC, hχ, _, hdata⟩ := hcut k (le_max_left _ _)
  apply dominated_subcaloric_unique_with_cutoff hG02 X o h U P ρ hloc u hu μ hμ hT hC hβ
    (k := k) (le_max_right _ _) hχ hz
  · intro x t ht
    have hx := hdata x t ht
    exact ⟨hx.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩
  · exact hzbound
  · exact hcal

end Yau.F04Proof
