import Yau.Proofs.F01ActualCharts

/-! Source and component properties of the EXPLICIT rescaled chart.
The final metric comparison uses this parametrization itself, rather than
identifying a chart obtained from an unrelated existential choice. -/
open Set Metric TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem rescaled_chart_ball_source_component (u : M.Carrier → ℝ) (o p : M.Carrier)
    {L : ℝ} (hL : 0 < L) (hp : p ∈ sublevelComponent u o L)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (b z₀ : ComplexVector n) {r c δ A : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hcr : c ≤ r / 12) (hA : 0 ≤ A)
    (hz₀ : z₀ ∈ closedBall b r) (hcenter : e z₀ = p)
    (hbuffer : ball b (4 * r) ⊆ e.source)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbase : 1 - u (e z₀) / L = δ)
    (huE : ContDiffOn ℝ ∞ (fun z => u (e z)) (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ (fun z => u (e z)) y‖ ≤ A)
    (hbudget : 2 * c * A / L ≤ 1 / 2) (hs : ((c * δ : ℝ) : ℂ) ≠ 0) :
    ball (0 : ComplexVector n) 2 ⊆ (rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs).source ∧
      MapsTo (rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs) (ball (0 : ComplexVector n) 2)
        (sublevelComponent u o L) := by
  let eR := rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs
  have hseg (z : ComplexVector n) (hz : z ∈ closedBall (0 : ComplexVector n) 2)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z₀ + (t * (c * δ)) • z ∈ ball b (4 * r) := by
    have hparam : (z₀, δ, z) ∈ closedBall b r ×ˢ
        (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ComplexVector n) 2) := ⟨hz₀, ⟨hδ.le, hδ1⟩, hz⟩
    exact bufferParameters_segment_mem (E := ComplexVector n) b hr hc.le hcr
      (θ := (z₀, δ, z)) (compact_parameters_subset_buffer b hr hparam) ht
  have hsource : ball (0 : ComplexVector n) 2 ⊆ eR.source := by
    intro z hz
    refine ⟨mem_univ z, ?_⟩
    change z₀ + ((c * δ : ℝ) : ℂ) • z ∈ e.source
    have h := hbuffer (hseg z (ball_subset_closedBall hz) 1 ⟨by norm_num, le_rfl⟩)
    simpa only [one_mul, Complex.coe_smul] using h
  refine ⟨hsource, ?_⟩
  change MapsTo eR (ball (0 : ComplexVector n) 2) (connectedComponentIn {x | u x < L} o)
  apply chart_ball_image_mem_component hp (by norm_num : (0 : ℝ) < 2)
    ((rescaledChart_contMDiffOn e he z₀ _ hs).continuousOn.mono hsource)
  · simpa only [eR, rescaledChart_center] using hcenter
  · intro z hz
    have hn : ‖z‖ ≤ 2 := (show ‖z‖ < 2 by simpa only [mem_ball, dist_zero_right] using hz).le
    have hpoint := rescaled_point_below_level isOpen_ball huE z₀ z hL hc.le hA hδ hbase hn
      (hseg z (ball_subset_closedBall hz))
      (fun t ht => hD _ (hseg z (ball_subset_closedBall hz) t ht)) hbudget
    change u (eR z) < L
    simpa only [eR, rescaledChart_apply, Complex.coe_smul] using hpoint

theorem explicit_rescaled_sublevel_chart_properties
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (o : M.Carrier) {L : ℝ}
    (hL : 0 < L) (ho : u o < L) (p : M.Carrier) (hp : p ∈ sublevelComponent u o L)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (hei : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target)
    (b z₀ : ComplexVector n) {r c δ A : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hcr : c ≤ r / 12) (hA : 0 ≤ A)
    (hz₀ : z₀ ∈ closedBall b r) (hcenter : e z₀ = p)
    (hbuffer : ball b (4 * r) ⊆ e.source)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbase : 1 - u (e z₀) / L = δ)
    (huE : ContDiffOn ℝ ∞ (fun z => u (e z)) (ball b (4 * r)))
    (hD : ∀ y ∈ ball b (4 * r), ‖fderiv ℝ (fun z => u (e z)) y‖ ≤ A)
    (hbudget : 2 * c * A / L ≤ 1 / 2) (hs : ((c * δ : ℝ) : ℂ) ≠ 0) :
    let S := sublevelOpens M u hu o L
    let hS : IsConnected (S : Set M.Carrier) := sublevelComponent_isConnected ho
    let eL := openRestrictedChart M S hS (rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs)
    eL 0 = (⟨p, hp⟩ : (sublevelManifold M u hu o L ho).Carrier) ∧
      closedBall (0 : ComplexVector n) 1 ⊆ eL.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eL eL.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eL.symm eL.target := by
  let S := sublevelOpens M u hu o L
  have hS : IsConnected (S : Set M.Carrier) := sublevelComponent_isConnected ho
  let eR := rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hs
  let eL := openRestrictedChart M S hS eR
  obtain ⟨hsource, hcomp⟩ := rescaled_chart_ball_source_component M u o p hL hp e he b z₀
    hr hc hcr hA hz₀ hcenter hbuffer hδ hδ1 hbase huE hD hbudget hs
  have hsource1 : closedBall (0 : ComplexVector n) 1 ⊆ eL.source := by
    intro z hz
    have hz2 : z ∈ ball (0 : ComplexVector n) 2 :=
      mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (by norm_num))
    exact mem_targetRestriction_source eR S hS.nonempty.to_subtype (hsource hz2) (hcomp hz2)
  refine ⟨?_, hsource1, ?_, ?_⟩
  · apply Subtype.ext
    exact (targetRestriction_value eR S hS.nonempty.to_subtype
      (hsource1 (mem_closedBall_self (by norm_num)))).trans
      ((rescaledChart_center e z₀ ((c * δ : ℝ) : ℂ) hs).trans hcenter)
  · exact targetRestriction_contMDiffOn eR S hS.nonempty.to_subtype
      (rescaledChart_contMDiffOn e he z₀ _ hs)
  · exact targetRestriction_inverse_contMDiffOn eR S hS.nonempty.to_subtype
      (rescaledChart_inverse_contMDiffOn e hei z₀ _ hs)

end Yau.NodeProofs.F01Aux
