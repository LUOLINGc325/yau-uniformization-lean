import spec.CHAIN.CONTRACTS

/-! The actual FTC identity behind the smooth boundary cancellation in the
rescaled conformal charts. It includes the zero-scale case without division. -/
open Set MeasureTheory
open scoped ContDiff Interval
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaled_segment_integral_fderiv {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) (z v : E) (a : ℝ)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + (t * a) • v ∈ U) :
    a * (∫ t in (0 : ℝ)..1, fderiv ℝ u (z + (t * a) • v) v) =
      u (z + a • v) - u z := by
  have hpath : Continuous (fun t : ℝ => z + (t * a) • v) := by fun_prop
  have hD : ContinuousOn (fun t : ℝ => fderiv ℝ u (z + (t * a) • v) v) (Icc 0 1) :=
    (((hu.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn.comp
      hpath.continuousOn hseg).clm_apply continuousOn_const)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => u (z + (s * a) • v))
        (a * fderiv ℝ u (z + (t * a) • v) v) t := by
    have hl : HasDerivAt (fun s : ℝ => z + (s * a) • v) (a • v) t := by
      simpa only [id_eq, one_mul] using
        (((hasDerivAt_id t).mul_const a).smul_const v).const_add z
    have hf := ((hu.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)).hasFDerivAt.comp_hasDerivAt t hl
    simpa only [Function.comp_def, map_smul, smul_eq_mul] using hf
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    ((hD.const_mul a).intervalIntegrable_of_Icc zero_le_one)
  simpa only [intervalIntegral.integral_const_mul, one_mul, zero_mul, zero_smul,
    add_zero] using hFTC

end Yau.NodeProofs.F01Aux
