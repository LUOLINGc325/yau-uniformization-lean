import Yau.LeafProofs.L16ExpBoundaryData
import Yau.LeafProofs.L09

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem definingFunction_nonpos_on_closure {E : Type*} [TopologicalSpace E]
    {O V : Set E} {ρ : E → ℝ} (hV : IsOpen V) (hρ : ContinuousOn ρ V)
    (hdef : O ∩ V = {y | y ∈ V ∧ ρ y < 0})
    {y : E} (hy : y ∈ closure O) (hyV : y ∈ V) : ρ y ≤ 0 := by
  apply ContinuousWithinAt.closure_le (hV.closure_inter ⟨hy,hyV⟩)
    ((hρ.continuousAt (hV.mem_nhds hyV)).continuousWithinAt) continuousWithinAt_const
  intro z hz
  exact ((Set.ext_iff.mp hdef z).mp hz).2.le

/-- Each genuine defining function has an ambient neighborhood with bounded
jets and a uniformly nonvanishing gradient. The construction precedes every
coefficient field and every candidate solution. -/
theorem smoothDomain_local_defining_data {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {x : Space n} (hx : x ∈ frontier O) :
    ∃ (s : Space n → ℝ) (R a₀ M₁ M₂ S₀ : ℝ),
      0 < R ∧ 0 < a₀ ∧ 0 < M₁ ∧ 0 < M₂ ∧ 0 < S₀ ∧
      (∀ z ∈ Metric.ball x R, ContDiffAt ℝ 2 s z) ∧
      (∀ z ∈ Metric.ball x R, a₀ ≤ ‖fderiv ℝ s z‖ ∧
        ‖fderiv ℝ s z‖ ≤ M₁ ∧ ‖fderiv ℝ (fderiv ℝ s) z‖ ≤ M₂ ∧ |s z| ≤ S₀) ∧
      (∀ z ∈ closure O ∩ Metric.ball x R, 0 ≤ s z) ∧
      ∀ z ∈ frontier O ∩ Metric.ball x R, s z = 0 := by
  obtain ⟨V,ρ,hV,hxV,hρ,hρx,hL,hdef⟩ := hO.2.2.2 x hx
  let s : Space n → ℝ := fun z => -ρ z
  have hs : ContDiffAt ℝ 3 s x :=
    ((hρ.contDiffAt (hV.mem_nhds hxV)).of_le (by simp)).neg
  have hn : 0 < ‖fderiv ℝ s x‖ := by
    apply norm_pos_iff.mpr
    simpa only [s,fderiv_fun_neg,neg_ne_zero] using hL
  have hc₁ : ContinuousAt (fun z => ‖fderiv ℝ s z‖) x :=
    (hs.fderiv_right (m := 2) (by norm_num)).continuousAt.norm
  have hc₂ : ContinuousAt (fun z => ‖fderiv ℝ (fderiv ℝ s) z‖) x :=
    ((hs.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).continuousAt.norm
  have hc₀ : ContinuousAt (fun z => |s z|) x := hs.continuousAt.abs
  have hlo : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ s x‖/2 < ‖fderiv ℝ s z‖ :=
    hc₁.eventually (lt_mem_nhds (by linarith : ‖fderiv ℝ s x‖/2 < ‖fderiv ℝ s x‖))
  have hhi₁ : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ s z‖ < ‖fderiv ℝ s x‖+1 :=
    hc₁.eventually (gt_mem_nhds (lt_add_one _))
  have hhi₂ : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ (fderiv ℝ s) z‖ < ‖fderiv ℝ (fderiv ℝ s) x‖+1 :=
    hc₂.eventually (gt_mem_nhds (lt_add_one _))
  have hhi₀ : ∀ᶠ z in 𝓝 x, |s z| < |s x|+1 :=
    hc₀.eventually (gt_mem_nhds (lt_add_one _))
  have hall : ∀ᶠ z in 𝓝 x, z ∈ V ∧ ‖fderiv ℝ s x‖/2 < ‖fderiv ℝ s z‖ ∧
      ‖fderiv ℝ s z‖ < ‖fderiv ℝ s x‖+1 ∧
      ‖fderiv ℝ (fderiv ℝ s) z‖ < ‖fderiv ℝ (fderiv ℝ s) x‖+1 ∧ |s z| < |s x|+1 := by
    filter_upwards [hV.mem_nhds hxV,hlo,hhi₁,hhi₂,hhi₀] with z hz hl h₁ h₂ h₀
    exact ⟨hz,hl,h₁,h₂,h₀⟩
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨s,R,‖fderiv ℝ s x‖/2,‖fderiv ℝ s x‖+1,
    ‖fderiv ℝ (fderiv ℝ s) x‖+1,|s x|+1,hR,by positivity,by positivity,
    by positivity,by positivity,?_,?_,?_,?_⟩
  · intro z hz
    exact ((hρ.contDiffAt (hV.mem_nhds (hball hz).1)).of_le (by simp)).neg
  · intro z hz
    exact ⟨(hball hz).2.1.le,(hball hz).2.2.1.le,
      (hball hz).2.2.2.1.le,(hball hz).2.2.2.2.le⟩
  · intro z hz
    exact neg_nonneg.mpr (definingFunction_nonpos_on_closure hV hρ.continuousOn hdef
      hz.1 (hball hz.2).1)
  · intro z hz
    exact neg_eq_zero.mpr (L16Aux.definingFunction_zero_on_frontier hO.1 hV
      hρ.continuousOn hdef hz.1 (hball hz.2).1)

theorem defining_data_gradient_coordinates {n : ℕ} (s : Space n → ℝ) (x : Space n) :
    ‖fderiv ℝ s x‖^2 = ∑ i, (d s x i)^2 := by
  simpa only [d,Yau.LeafProofs.complexVector_realOrthonormalBasis_apply] using
    (Yau.LeafProofs.complexVector_realOrthonormalBasis n).norm_dual (fderiv ℝ s x)

end Yau.LeafProofs.L16ExpBoundaryAux
