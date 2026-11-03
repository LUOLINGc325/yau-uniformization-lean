import Yau.LeafProofs.L05ABPViscosityApprox
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- A genuine compact-buffer extension, with no bound or continuity imposed
on the original function away from the actual buffer. -/
theorem jet_exists_bounded_extension {n : ℕ} {u : Point n → ℝ} {D : Set (Point n)}
    (hD : IsCompact D) (hu : ContinuousOn u D) :
    ∃ (B : ℝ) (U : Point n → ℝ), 0 < B ∧ Continuous U ∧
      (∀ z, |U z| ≤ B) ∧ EqOn U u D := by
  obtain ⟨C,hC⟩ := hD.exists_bound_of_continuousOn hu
  let B : ℝ := |C|+1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hLocal (x : D) : |u x| ≤ B := by
    have h := hC x x.property
    rw [Real.norm_eq_abs] at h
    exact h.trans (by dsimp only [B]; linarith [le_abs_self C])
  let f : C(D,ℝ) := ⟨fun x => u x,hu.domRestrict⟩
  obtain ⟨U,hRange,hEq⟩ := f.exists_restrict_eq_forall_mem_of_closed
    (t := Icc (-B) B) (fun x => abs_le.mp (hLocal x))
    ⟨0,by constructor <;> linarith only [hB]⟩ hD.isClosed
  refine ⟨B,U,hB,U.continuous,fun z => abs_le.mpr (hRange z),?_⟩
  intro x hx
  exact congrArg (fun k : C(D,ℝ) => k ⟨x,hx⟩) hEq

theorem jet_touchAbove_of_eventuallyEq {n : ℕ} {U u phi : Point n → ℝ} {p : Point n}
    (heq : U =ᶠ[𝓝 p] u) (ht : touchAbove phi U p) : touchAbove phi u p := by
  refine ⟨ht.1.trans heq.eq_of_nhds,?_⟩
  filter_upwards [heq,ht.2] with q hq hUpper
  rw [← hq]
  exact hUpper

theorem jet_eventuallyEq_of_eqOn {n : ℕ} {U u : Point n → ℝ} {p : Point n}
    {D : Set (Point n)} (hEq : EqOn U u D) (hD : D ∈ 𝓝 p) : U =ᶠ[𝓝 p] u := by
  filter_upwards [hD] with q hq
  exact hEq hq

/-- Bounded continuous sources converge locally uniformly under the actual
joint sup convolution. The modulus is obtained on a compact buffer, rather
than imposed globally on the original source. -/
theorem jet_sup_uniform_on_closedBall {n : ℕ} {U : Point n → ℝ} {B R a : ℝ}
    (hU : Continuous U) (hB : 0 < B) (hb : ∀ z, |U z| ≤ B)
    (p : Point n) (hR : 0 < R) (ha : 0 < a) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∀ z ∈ Metric.closedBall p (R/2), |supRegularize eps U z-U z| < a := by
  have hUC : UniformContinuousOn U (Metric.closedBall p R) :=
    (isCompact_closedBall p R).uniformContinuousOn_of_continuous hU.continuousOn
  obtain ⟨ρ,hρ,hMod⟩ := Metric.uniformContinuousOn_iff.mp hUC a ha
  let d : ℝ := min ρ (R/2)
  have hd : 0 < d := lt_min hρ (by positivity)
  have hdρ : d ≤ ρ := min_le_left _ _
  have hdR : d ≤ R/2 := min_le_right _ _
  refine ⟨d^2/(4*B),by positivity,?_⟩
  intro eps heps hSmall z hz
  have hScale : 4*B*eps < d^2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*B)).mp hSmall
    nlinarith only [h]
  obtain ⟨q,hq,_,hDisp⟩ := supRegularize_attained hU hB.le hb heps z
  have hDist : dist q z < d := by
    rw [dist_eq_norm,norm_sub_rev]
    have h := (norm_sq_le_qnorm2 (z-q)).trans hDisp
    nlinarith only [h,hScale,hd,norm_nonneg (z-q)]
  have hzR : z ∈ Metric.closedBall p R :=
    Metric.closedBall_subset_closedBall (by linarith only [hR] : R/2 ≤ R) hz
  have hqR : q ∈ Metric.closedBall p R := by
    apply Metric.mem_closedBall.mpr
    have hzDist := Metric.mem_closedBall.mp hz
    linarith [dist_triangle q z p]
  have hDiff := hMod q hqR z hzR (hDist.trans_le hdρ)
  rw [Real.dist_eq] at hDiff
  have hLower := (supRegularize_bounds hU hB.le hb heps z).1
  rw [abs_of_nonneg (sub_nonneg.mpr hLower),hq]
  have hPenalty : 0 ≤ qnorm2 (z-q)/(2*eps) :=
    div_nonneg (qnorm2_nonneg _) (by positivity)
  linarith [le_abs_self (U q-U z)]

end Yau.LeafProofs.L05Aux
