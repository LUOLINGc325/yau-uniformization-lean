import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- Testing local L¹ convergence against a bounded continuous weight. -/
theorem tendsto_integral_mul_of_L1 {K : Set ℂ} (hK : IsCompact K)
    {v : ℕ → ℂ → ℝ} {u φ : ℂ → ℝ}
    (hv : ∀ j, IntegrableOn (v j) K volume) (hu : IntegrableOn u K volume)
    (hφ : ContinuousOn φ K)
    (hconv : Tendsto (fun j ↦ ∫ z in K, |v j z - u z|) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ z in K, v j z * φ z) atTop
      (𝓝 (∫ z in K, u z * φ z)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ
  have hzero : Tendsto (fun j ↦ C * ∫ z in K, |v j z - u z|) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hconv
  have hφv (j : ℕ) : IntegrableOn (fun z ↦ v j z * φ z) K volume :=
    (hv j).mul_continuousOn hφ hK
  have hφu : IntegrableOn (fun z ↦ u z * φ z) K volume :=
    hu.mul_continuousOn hφ hK
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hzero).2 ε hε)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [Real.dist_eq, ← integral_sub (hφv j) hφu]
  have hnorm : |∫ z in K, v j z * φ z - u z * φ z| ≤
      ∫ z in K, |v j z - u z| * C := by
    calc
      _ ≤ ∫ z in K, |v j z * φ z - u z * φ z| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun z ↦ v j z * φ z - u z * φ z) (μ := volume.restrict K)
      _ ≤ ∫ z in K, |v j z - u z| * C := by
        apply integral_mono_ae ((hφv j).sub hφu).abs (((hv j).sub hu).abs.mul_const C)
        filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
        change |v j z * φ z - u z * φ z| ≤ |v j z - u z| * C
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC z hz) (abs_nonneg _)
  rw [integral_mul_const, mul_comm] at hnorm
  exact hnorm.trans_lt (hN j hj)

/-- Local L¹ convergence gives ordinary distributional convergence once the
Green identity has moved the derivatives to the compactly supported test. -/
theorem tendsto_pairing_of_Green {U : Set ℂ} {v : ℕ → ℂ → ℝ} {u ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hv : ∀ j, IntegrableOn (v j) (tsupport ψ) volume)
    (hu : IntegrableOn u (tsupport ψ) volume)
    (hconv : Tendsto (fun j ↦ ∫ z in tsupport ψ, |v j z - u z|) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ z, v j z * ψ z) atTop (𝓝 (∫ z, u z * ψ z)) := by
  have hv_eq (j : ℕ) : (∫ z in tsupport ψ, v j z * ψ z) = ∫ z, v j z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hu_eq : (∫ z in tsupport ψ, u z * ψ z) = ∫ z, u z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  simpa only [hv_eq, hu_eq] using tendsto_integral_mul_of_L1 hψc hv hu hψ.continuousOn hconv

end Yau.NodeProofs.D02RieszAux
