import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Uniform local domination in the Banach parameter of a compact interval integral. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Yau.Proofs.C04Aux

universe u
variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem radialIntegral_compact_parameter_bound (H : E × ℝ → G) (hH : Continuous H) (x : E) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, ‖H (y,t)‖ ≤ C := by
  have hslice : Continuous (fun t : ℝ => H (x,t)) :=
    hH.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hslice.continuousOn
  let D := max C 0 + 1
  have hD : 0 < D := by dsimp only [D]; have := le_max_right C 0; linarith
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (x,t)‖ < D := by
    intro t ht
    have hh := hC t ht
    dsimp only [D]
    have := le_max_left C 0
    linarith
  have he := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).eventually_forall_of_forall_eventually
    (P := fun y t => ‖H (y,t)‖ < D) (fun t ht => hH.continuousAt.norm.eventually_lt_const (hb t ht))
  exact ⟨D, hD, he.mono fun y hy t ht => (hy t ht).le⟩

def radialIntegralPartial (H : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ H p).comp ((ContinuousLinearMap.id ℝ E).prod 0)

theorem radialIntegralPartial_hasFDerivAt (H : E × ℝ → G) {p : E × ℝ}
    (hH : DifferentiableAt ℝ H p) :
    HasFDerivAt (fun x => H (x,p.2)) (radialIntegralPartial H p) p.1 := by
  exact hH.hasFDerivAt.comp p.1
    ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))

theorem radialIntegralPartial_contDiff {H : E × ℝ → G} (n : ℕ)
    (hH : ContDiff ℝ (n + 1) H) : ContDiff ℝ n (radialIntegralPartial H) := by
  exact (hH.fderiv_right (by simp)).clm_comp contDiff_const

theorem radialIntegral_joint_continuous (H : E × ℝ → G) (hH : Continuous H) :
    Continuous (fun x => ∫ t in (0 : ℝ)..1, H (x,t)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨C, hC, hbound⟩ := radialIntegral_compact_parameter_bound H hH x
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ : ℝ => C)
  · exact Eventually.of_forall fun y => (hH.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hbound] with y hy
    apply Eventually.of_forall
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact hy t ⟨ht'.1.le, ht'.2⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht => (hH.comp (continuous_id.prodMk continuous_const)).continuousAt

theorem radialIntegral_joint_hasFDerivAt (H : E × ℝ → G) (hH : ContDiff ℝ 1 H) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, H (y,t))
      (∫ t in (0 : ℝ)..1, radialIntegralPartial H (x,t)) x := by
  have hD : Continuous (radialIntegralPartial H) :=
    (radialIntegralPartial_contDiff 0 (by simpa using hH)).continuous
  obtain ⟨C, hC, hbound⟩ := radialIntegral_compact_parameter_bound (radialIntegralPartial H) hD x
  let U : Set E := {y | ∀ t ∈ Icc (0 : ℝ) 1, ‖radialIntegralPartial H (y,t)‖ ≤ C}
  have hU : U ∈ 𝓝 x := hbound
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := U) (F' := fun y t => radialIntegralPartial H (y,t)) (bound := fun _ : ℝ => C) hU
  · exact Eventually.of_forall fun y => (hH.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hH.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro t ht y hy
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact hy t ⟨ht'.1.le, ht'.2⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht y hy => radialIntegralPartial_hasFDerivAt H
      (hH.differentiable (by norm_num) (y,t))

theorem radialIntegral_joint_contDiff_nat (H : E × ℝ → G) (n : ℕ) (hH : ContDiff ℝ n H) :
    ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, H (x,t)) := by
  induction n generalizing G with
  | zero => exact contDiff_zero.mpr (radialIntegral_joint_continuous H hH.continuous)
  | succ n IH =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ t in (0 : ℝ)..1, radialIntegralPartial H (x,t), ?_, ?_⟩
    · exact IH _ (radialIntegralPartial_contDiff n hH)
    · exact radialIntegral_joint_hasFDerivAt H (hH.of_le (by simp))

theorem radialIntegral_joint_contDiff (H : E × ℝ → G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, H (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  exact radialIntegral_joint_contDiff_nat H n (hH.of_le (by simp))

end Yau.Proofs.C04Aux
