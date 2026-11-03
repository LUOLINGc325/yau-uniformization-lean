import Yau.LeafProofs.L16TraceSpatialDifferentiation

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceSpatialGradient_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceSpatialGradient_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Genuine first tangent-kernel integrability up to the normal face. -/
theorem normalTraceTangential_integrable {n : ℕ} {F t a : ℝ}
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ξ : Space n) :
    IntervalIntegrable (fun r => normalHeatProfile r a •
      fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ) volume 0 t := by
  rcases ht.eq_or_lt with rfl | ht
  · exact IntervalIntegrable.refl
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  have hμ : volume.restrict (Ioo (0 : ℝ) t) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono_set volume (fun _ hr => hr.1)
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (retardedHeatAverage_fderiv_time_integrable hB hF ht ξ)).bdd_smul 1
    ((normalHeatProfile_time_aestronglyMeasurable a).mono_measure hμ) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [Real.norm_eq_abs,abs_of_nonneg (normalHeatProfile_bounds hr.1 ha).1]
      exact (normalHeatProfile_bounds hr.1 ha).2)

/-- The actual gradient field in physical spatial coordinates. -/
def boundaryTraceGradient {n : ℕ} (e : Space n) (B : Point n → ℝ) (p : Point n) :
    Space n →L[ℝ] ℝ :=
  (normalTraceTangential B p.2 (inner ℝ e p.1) (halfSpaceBoundaryProjection e p.1)).comp
    (halfSpaceBoundaryProjection e) +
  normalTraceFirst B (halfSpaceBoundaryProjection e p.1) p.2 (inner ℝ e p.1) • innerSL ℝ e

/-- All terms of the true physical gradient kernel are integrable, including
    at zero height and initial time. Its integral is the explicit field. -/
theorem traceSpatialGradientKernel_integral {n : ℕ} {F t : ℝ}
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (ht : 0 ≤ t) (e x : Space n) (hx : 0 ≤ inner ℝ e x) :
    IntervalIntegrable (traceSpatialGradientKernel e B t x) volume 0 t ∧
      (∫ r in (0 : ℝ)..t, traceSpatialGradientKernel e B t x r) = boundaryTraceGradient e B (x,t) := by
  let P := halfSpaceBoundaryProjection e
  let N := innerSL ℝ e
  let L : (Space n →L[ℝ] ℝ) →L[ℝ] (Space n →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip P
  let f : ℝ → Space n →L[ℝ] ℝ := fun r => normalHeatProfile r (inner ℝ e x) •
    fderiv ℝ (heatAverage r (fun y => B (y,t-r))) (P x)
  let g : ℝ → ℝ := fun r => 2*normalGaussianKernel r (inner ℝ e x)*
    heatAverage r (fun y => B (y,t-r)) (P x)
  have hf : IntervalIntegrable f volume 0 t := normalTraceTangential_integrable hB hF ht hx (P x)
  have hg : IntervalIntegrable g volume 0 t := (normalTraceLayer_hasDerivAt hB hF ht hx (P x)).1
  have hLI : IntervalIntegrable (fun r => L (f r)) volume 0 t :=
    ⟨L.integrable_comp hf.1,L.integrable_comp hf.2⟩
  have hNI : IntervalIntegrable (fun r => g r • N) volume 0 t :=
    ⟨hg.1.smul_const N,hg.2.smul_const N⟩
  have hFun : traceSpatialGradientKernel e B t x = fun r => L (f r)+g r • N := by
    funext r
    simp only [traceSpatialGradientKernel,L,f,g,P,N,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply,map_smul]
  rw [hFun]
  refine ⟨hLI.add hNI,?_⟩
  rw [intervalIntegral.integral_add hLI hNI,L.intervalIntegral_comp_comm hf,
    intervalIntegral.integral_smul_const]
  rfl

/-- The explicit physical gradient is an actual Fréchet derivative on the
    strict half space, with the true initial time included. -/
theorem boundaryTraceLayer_hasFDerivAt_gradient {n : ℕ} {F t : ℝ}
    {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (ht : 0 ≤ t)
    {x : Space n} (hx : 0 < inner ℝ e x) :
    HasFDerivAt (fun z => boundaryTraceLayer e B (z,t)) (boundaryTraceGradient e B (x,t)) x := by
  rcases ht.eq_or_lt with rfl | ht
  · have hFun : (fun z => boundaryTraceLayer e B (z,0)) = fun _ : Space n => (0 : ℝ) := by
      funext z
      exact normalTraceLayer_initial B _ _
    have hG : boundaryTraceGradient e B (x,0) = 0 := by
      simp [boundaryTraceGradient,normalTraceTangential_initial,normalTraceFirst]
    rw [hFun,hG]
    exact hasFDerivAt_const 0 x
  · have h := (boundaryTraceLayer_hasFDerivAt he hB hF ht hx).2
    rwa [(traceSpatialGradientKernel_integral hB hF ht.le e x hx.le).2] at h

/-- A uniform quantitative bound for the actual spatial gradient field,
    including both the normal face and the zero initial slice. -/
theorem boundaryTraceGradient_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ (B : Point n → ℝ) (F : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → ∀ t : ℝ, 0 ≤ t → ∀ x : Space n,
      0 ≤ inner ℝ e x → ‖boundaryTraceGradient e B (x,t)‖ ≤ C*F*t^(1/2 : ℝ) := by
  obtain ⟨C,hC,hKBound⟩ := traceSpatialGradientKernel_bound (n := n)
  refine ⟨2*C,by positivity,?_⟩
  intro e he B F hB hF t ht x hx
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  rcases ht.eq_or_lt with rfl | ht
  · simp only [boundaryTraceGradient,normalTraceTangential_initial,ContinuousLinearMap.zero_comp,
      normalTraceFirst,intervalIntegral.integral_same,zero_smul,add_zero,norm_zero]
    positivity
  have hPower : IntervalIntegrable (fun r : ℝ => r^(-(1/2 : ℝ))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hBI : Integrable (fun r : ℝ => C*F*r^(-(1/2 : ℝ))) (volume.restrict (Ioo 0 t)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp (hPower.const_mul (C*F))
  have hInt : (∫ r in Ioo (0 : ℝ) t, r^(-(1/2 : ℝ))) = 2*t^(1/2 : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ht.le,
      integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1/2 : ℝ))),
      show -(1/2 : ℝ)+1 = (1/2 : ℝ) by ring,Real.zero_rpow (by norm_num : (1/2 : ℝ) ≠ 0),sub_zero]
    ring
  rw [← (traceSpatialGradientKernel_integral hB hF ht.le e x hx).2,
    intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ r in Ioo (0 : ℝ) t, C*F*r^(-(1/2 : ℝ)) := by
      apply norm_integral_le_of_norm_le hBI
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hKBound e he B F hB hF r hr.1 t x hx
    _ = (2*C)*F*t^(1/2 : ℝ) := by rw [integral_const_mul,hInt]; ring

end Yau.LeafProofs.L16Aux
