import Yau.Proofs.V03Fourier

/-! The homogeneous half-derivative seminorm is bounded by the angular
derivative's L² norm. This supplies finiteness and the topology used in radial
convergence without discarding the logarithmic wall term. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleFourier_weight_le_derivative {u u' : ℝ → ℂ}
    (hu : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (u' θ) θ)
    (hu' : IntervalIntegrable u' volume 0 (2 * Real.pi))
    (hperiod : u (2 * Real.pi) = u 0) (k : ℤ) :
    |(k : ℝ)| * ‖circleFourier u k‖ ^ 2 ≤ ‖circleFourier u' k‖ ^ 2 := by
  by_cases hk : k = 0
  · simp [hk]
  have hIk : Complex.I * (k : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
  have hc : Complex.I * (k : ℂ) * circleFourier u k = circleFourier u' k := by
    rw [circleFourier_of_hasDerivAt hk hu hu' hperiod,
      ← mul_assoc, mul_inv_cancel₀ hIk, one_mul]
  have hn := congrArg norm hc
  simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, one_mul] at hn
  rw [← hn]
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hi : (1 : ℕ) ≤ k.natAbs := Int.natAbs_pos.mpr hk
    have hic : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hi
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hic
  calc
    |(k : ℝ)| * ‖circleFourier u k‖ ^ 2 ≤
        |(k : ℝ)| ^ 2 * ‖circleFourier u k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ = _ := by ring

theorem boundaryDSq_le_angularDerivative {u u' : ℝ → ℂ}
    (hu : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (u' θ) θ)
    (hu' : IntervalIntegrable u' volume 0 (2 * Real.pi))
    (hperiod : u (2 * Real.pi) = u 0)
    (hLp : MemLp u' 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :
    boundaryDSq (fun θ (_ : Unit) => u θ) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖u' θ‖ ^ 2) := by
  have hp := circleFourier_parseval hLp
  calc
    boundaryDSq (fun θ (_ : Unit) => u θ) =
        ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| * ‖circleFourier u k‖ ^ 2) := by
      simp [boundaryDSq, Int.cast_abs]
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (‖circleFourier u' k‖ ^ 2) :=
      ENNReal.tsum_le_tsum fun k =>
        ENNReal.ofReal_le_ofReal (circleFourier_weight_le_derivative hu hu' hperiod k)
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖u' θ‖ ^ 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hp.summable,
        hp.tsum_eq]

theorem boundaryDSq_ne_top_of_angularDerivative {u u' : ℝ → ℂ}
    (hu : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (u' θ) θ)
    (hu' : IntervalIntegrable u' volume 0 (2 * Real.pi))
    (hperiod : u (2 * Real.pi) = u 0)
    (hLp : MemLp u' 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :
    boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (boundaryDSq_le_angularDerivative hu hu' hperiod hLp)

theorem continuous_memLp_circleInterval {u : ℝ → ℂ} (hu : Continuous u) :
    MemLp u 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi))).image
      hu).isBounded.exists_norm_le
  apply MemLp.of_bound hu.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact hC (u θ) ⟨θ, ⟨hθ.1.le, hθ.2⟩, rfl⟩

theorem boundaryDSq_ne_top_of_periodic_C1 {u u' : ℝ → ℂ}
    (hu : ∀ θ, HasDerivAt u (u' θ) θ) (hu' : Continuous u')
    (hperiod : u (2 * Real.pi) = u 0) :
    boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤ :=
  boundaryDSq_ne_top_of_angularDerivative (fun θ _ => hu θ)
    (hu'.intervalIntegrable _ _) hperiod (continuous_memLp_circleInterval hu')

end Yau.Blueprint.V03Proof
