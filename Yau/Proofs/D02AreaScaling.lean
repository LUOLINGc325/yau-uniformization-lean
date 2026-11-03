import Yau.Proofs.D02PhysicalScaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Ordinary planar area under real parameter rescaling. -/

open scoped ENNReal
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem setLIntegral_real_smul (R : ℝ) (hR : R ≠ 0) (S : Set ℂ)
    (hS : MeasurableSet S) (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in (fun w : ℂ => R • w) ⁻¹' S, q (R • z) ∂volume) =
      ENNReal.ofReal (|R ^ 2|⁻¹) * ∫⁻ w in S, q w ∂volume := by
  have hE : MeasurableEmbedding (fun z : ℂ => R • z) :=
    (Homeomorph.smul (Units.mk0 R hR)).toMeasurableEquiv.measurableEmbedding
  rw [← lintegral_indicator (hS.preimage hE.measurable), ← lintegral_indicator hS]
  have hi : ((fun w : ℂ => R • w) ⁻¹' S).indicator (fun z => q (R • z)) =
      fun z => S.indicator q (R • z) := by
    ext z
    by_cases hz : R • z ∈ S
    · have hz' : z ∈ (fun w : ℂ => R • w) ⁻¹' S := hz
      rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz]
    · have hz' : z ∉ (fun w : ℂ => R • w) ⁻¹' S := hz
      rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
  rw [hi, ← hE.lintegral_map (S.indicator q), Measure.map_addHaar_smul volume hR,
    lintegral_smul_measure]
  simp only [Complex.finrank_real_complex, smul_eq_mul, abs_inv]

/-- Both the squared derivative and the planar area Jacobian are retained.
The resulting physical weighted integral has the exact factor R^σ. -/
theorem weighted_setLIntegral_rescale (R : ℝ) (hR : 0 < R) (ρ σ : ℝ)
    (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ},
      ENNReal.ofReal (R ^ 2) * q (R • z) * ENNReal.ofReal (‖z‖ ^ (-σ)) ∂volume) =
      ENNReal.ofReal (R ^ σ) *
        ∫⁻ w in {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R * ρ},
          q w * ENNReal.ofReal (‖w‖ ^ (-σ)) ∂volume := by
  have hS : MeasurableSet {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R * ρ} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hpre : (fun z : ℂ => R • z) ⁻¹' {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < R * ρ} =
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ} := by
    ext z
    change (0 < ‖R • z‖ ∧ ‖R • z‖ < R * ρ) ↔ (0 < ‖z‖ ∧ ‖z‖ < ρ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    constructor
    · intro hz
      refine ⟨?_, ?_⟩ <;> nlinarith
    · intro hz
      refine ⟨mul_pos hR hz.1, ?_⟩
      nlinarith
  have hpow : R ^ (σ + 2) * R ^ (-σ) = R ^ 2 := by
    rw [← Real.rpow_add hR]
    have he : σ + 2 + -σ = (2 : ℝ) := by ring
    rw [he, Real.rpow_two]
  have hweight (z : ℂ) : R ^ 2 * ‖z‖ ^ (-σ) =
      R ^ (σ + 2) * ‖R • z‖ ^ (-σ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      Real.mul_rpow hR.le (norm_nonneg z), ← mul_assoc, hpow]
  have hi (z : ℂ) :
      ENNReal.ofReal (R ^ 2) * q (R • z) * ENNReal.ofReal (‖z‖ ^ (-σ)) =
      ENNReal.ofReal (R ^ (σ + 2)) *
        (q (R • z) * ENNReal.ofReal (‖R • z‖ ^ (-σ))) := by
    calc
      _ = (ENNReal.ofReal (R ^ 2) * ENNReal.ofReal (‖z‖ ^ (-σ))) * q (R • z) := by ring
      _ = ENNReal.ofReal (R ^ 2 * ‖z‖ ^ (-σ)) * q (R • z) := by
        rw [ENNReal.ofReal_mul (sq_nonneg R)]
      _ = ENNReal.ofReal (R ^ (σ + 2) * ‖R • z‖ ^ (-σ)) * q (R • z) := by rw [hweight]
      _ = _ := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]; ring
  simp_rw [hi]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hpre,
    setLIntegral_real_smul R hR.ne' _ hS
      (fun w => q w * ENNReal.ofReal (‖w‖ ^ (-σ)))]
  have hfactor : ENNReal.ofReal (R ^ (σ + 2)) * ENNReal.ofReal (|R ^ 2|⁻¹) =
      ENNReal.ofReal (R ^ σ) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    congr 1
    rw [abs_of_pos (sq_pos_of_pos hR), Real.rpow_add hR, Real.rpow_two]
    field_simp
  rw [← mul_assoc, hfactor]

end Yau.NodeProofs.D02Aux
