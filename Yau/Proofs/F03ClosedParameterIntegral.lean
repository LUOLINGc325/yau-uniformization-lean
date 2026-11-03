import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Genuine dominated C1 parameter integration on a convex closed slab, including its time faces. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace α]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem hasFDerivWithinAt_integral_of_dominated_lipschitz
    (μ : Measure α) (F : E → α → ℝ) (D : E → α → E →L[ℝ] ℝ)
    {S : Set E} (hS : Convex ℝ S) {x : E} (hx : x ∈ S)
    (B : α → ℝ) (hB : Integrable B μ) (hB0 : ∀ a,0 ≤ B a)
    (hInt : ∀ z ∈ S,Integrable (F z) μ)
    (hMeasD : ∀ z ∈ S,AEStronglyMeasurable (D z) μ)
    (hBound : ∀ a,∀ z ∈ S,‖D z a‖ ≤ B a)
    (hDeriv : ∀ a,∀ z ∈ S,HasFDerivWithinAt (fun w => F w a) (D z a) S z) :
    HasFDerivWithinAt (fun z => ∫ a,F z a ∂μ) (∫ a,D x a ∂μ) S x := by
  have hIntD : Integrable (D x) μ := hB.mono' (hMeasD x hx) (ae_of_all μ (fun a => hBound a x hx))
  have hLip (a : α) : LipschitzOnWith ⟨B a,hB0 a⟩ (fun z => F z a) S := by
    apply hS.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun z hz => hDeriv a z hz)
    intro z hz
    exact hBound a z hz
  have hNormEq : ∀ᶠ z in 𝓝[S] x,
      ‖z-x‖⁻¹*‖((∫ a,F z a ∂μ)-(∫ a,F x a ∂μ))-(∫ a,D x a ∂μ) (z-x)‖=
        ‖∫ a,‖z-x‖⁻¹ • (F z a-F x a-D x a (z-x)) ∂μ‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [← norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),integral_smul,
      integral_sub,integral_sub,← ContinuousLinearMap.integral_apply hIntD]
    exacts [hInt z hz,hInt x hx,(hInt z hz).sub (hInt x hx),hIntD.apply_continuousLinearMap _]
  rw [hasFDerivWithinAt_iff_tendsto,tendsto_congr' hNormEq,← tendsto_zero_iff_norm_tendsto_zero,
    ← show (∫ a,‖x-x‖⁻¹ • (F x a-F x a-D x a (x-x)) ∂μ)=0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun a => B a+‖D x a‖)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hm : AEStronglyMeasurable (fun a => F z a-F x a-D x a (z-x)) μ := by
      exact (((hInt z hz).aestronglyMeasurable.sub (hInt x hx).aestronglyMeasurable).sub
        ((hMeasD x hx).apply_continuousLinearMap (z-x))).congr
          (ae_of_all μ (fun a => rfl))
    exact (hm.const_smul (‖z-x‖⁻¹ : ℝ)).congr (ae_of_all μ (fun a => rfl))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    apply ae_of_all μ
    intro a
    have hL : ‖F z a-F x a‖ ≤ B a*‖z-x‖ := by
      have hh := (hLip a).dist_le_mul z hz x hx
      change dist (F z a) (F x a) ≤ B a*dist z x at hh
      simpa only [dist_eq_norm] using hh
    calc
      _ = ‖z-x‖⁻¹*‖F z a-F x a-D x a (z-x)‖ :=
        norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
      _ ≤ ‖z-x‖⁻¹*(‖F z a-F x a‖+‖D x a (z-x)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ ‖z-x‖⁻¹*(B a*‖z-x‖+‖D x a‖*‖z-x‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hL ((D x a).le_opNorm _)) (by positivity)
      _ ≤ B a+‖D x a‖ := by
        rw [mul_add]
        apply add_le_add
        · rw [← div_eq_inv_mul]
          exact div_le_of_le_mul₀ (norm_nonneg _) (hB0 a) le_rfl
        · rw [← div_eq_inv_mul]
          exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) le_rfl
  · exact hB.add hIntD.norm
  · apply ae_of_all μ
    intro a
    have h := hDeriv a x hx
    rw [hasFDerivWithinAt_iff_tendsto] at h
    simp only [sub_self,map_zero,sub_zero,smul_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using h

theorem contDiffOn_one_integral_of_dominated
    (μ : Measure α) (F : E → α → ℝ) (D : E → α → E →L[ℝ] ℝ)
    {S : Set E} (hS : Convex ℝ S) (hUnique : UniqueDiffOn ℝ S)
    (B : α → ℝ) (hB : Integrable B μ) (hB0 : ∀ a,0 ≤ B a)
    (hInt : ∀ z ∈ S,Integrable (F z) μ)
    (hMeasD : ∀ z ∈ S,AEStronglyMeasurable (D z) μ)
    (hBound : ∀ a,∀ z ∈ S,‖D z a‖ ≤ B a)
    (hDeriv : ∀ a,∀ z ∈ S,HasFDerivWithinAt (fun w => F w a) (D z a) S z)
    (hContinuousD : ∀ a,ContinuousOn (fun z => D z a) S) :
    ContDiffOn ℝ 1 (fun z => ∫ a,F z a ∂μ) S := by
  have hD (z : E) (hz : z ∈ S) := hasFDerivWithinAt_integral_of_dominated_lipschitz
    μ F D hS hz B hB hB0 hInt hMeasD hBound hDeriv
  have hCont : ContinuousOn (fun z => ∫ a,D z a ∂μ) S := by
    apply continuousOn_of_dominated hMeasD
    · exact fun z hz => ae_of_all μ (fun a => hBound a z hz)
    · exact hB
    · exact ae_of_all μ hContinuousD
  have hDiff : DifferentiableOn ℝ (fun z => ∫ a,F z a ∂μ) S :=
    fun z hz => (hD z hz).differentiableWithinAt
  rw [show (1 : ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_fderivWithin hUnique]
  refine ⟨hDiff,by norm_num,contDiffOn_zero.mpr ?_⟩
  apply hCont.congr
  intro z hz
  exact (hD z hz).fderivWithin (hUnique z hz)

end Yau.Proofs.F03Aux
