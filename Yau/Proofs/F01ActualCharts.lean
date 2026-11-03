import Yau.Proofs.F01RescaledGram
import Yau.Proofs.F01ConformalBackground
import Yau.Proofs.F01ChartComponent
import Yau.Proofs.F01ChartBuffer
import Yau.Proofs.F01BoundaryRatioBounds

/-! Actual holomorphic rescaled charts into the SAME sublevel component.
Only ordinary chart buffers and derivatives of the actual coordinate
exhaustion enter; the map and inverse are explicitly constructed. -/
open Set Metric TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n)

theorem exists_actual_rescaled_sublevel_chart
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
    (hbudget : 2 * c * A / L ≤ 1 / 2) :
    ∃ eL : OpenPartialHomeomorph (ComplexVector n) (sublevelManifold M u hu o L ho).Carrier,
      eL 0 = (⟨p, hp⟩ : (sublevelManifold M u hu o L ho).Carrier) ∧
      closedBall (0 : ComplexVector n) 1 ⊆ eL.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eL eL.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eL.symm eL.target := by
  let S := sublevelOpens M u hu o L
  have hS : IsConnected (S : Set M.Carrier) := sublevelComponent_isConnected ho
  have hscale : ((c * δ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos hc hδ).ne'
  let eR := rescaledChart e z₀ ((c * δ : ℝ) : ℂ) hscale
  have heR : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eR eR.source :=
    rescaledChart_contMDiffOn e he z₀ _ hscale
  have heiR : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ eR.symm eR.target :=
    rescaledChart_inverse_contMDiffOn e hei z₀ _ hscale
  have hseg (z : ComplexVector n) (hz : z ∈ closedBall (0 : ComplexVector n) 2)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z₀ + (t * (c * δ)) • z ∈ ball b (4 * r) := by
    have hparam : (z₀, δ, z) ∈ closedBall b r ×ˢ
        (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ComplexVector n) 2) :=
      ⟨hz₀, ⟨hδ.le, hδ1⟩, hz⟩
    have hθ : (z₀, δ, z) ∈ bufferParameters b r :=
      compact_parameters_subset_buffer (E := ComplexVector n) b hr hparam
    exact bufferParameters_segment_mem (E := ComplexVector n) b hr hc.le hcr
      (θ := (z₀, δ, z)) hθ ht
  have hsource2 : ball (0 : ComplexVector n) 2 ⊆ eR.source := by
    intro z hz
    refine ⟨mem_univ z, ?_⟩
    change z₀ + ((c * δ : ℝ) : ℂ) • z ∈ e.source
    have h := hbuffer (hseg z (ball_subset_closedBall hz) 1 ⟨by norm_num, le_rfl⟩)
    simpa only [one_mul, Complex.coe_smul] using h
  have hcomp : MapsTo eR (ball (0 : ComplexVector n) 2) (S : Set M.Carrier) := by
    change MapsTo eR (ball (0 : ComplexVector n) 2) (connectedComponentIn {x | u x < L} o)
    apply chart_ball_image_mem_component hp (by norm_num : (0 : ℝ) < 2)
      (heR.continuousOn.mono hsource2)
    · simpa only [eR, rescaledChart_center] using hcenter
    · intro z hz
      have hn : ‖z‖ ≤ 2 := (show ‖z‖ < 2 by simpa only [mem_ball, dist_zero_right] using hz).le
      have hpoint := rescaled_point_below_level isOpen_ball huE z₀ z hL hc.le hA hδ hbase hn
        (hseg z (ball_subset_closedBall hz))
        (fun t ht => hD _ (hseg z (ball_subset_closedBall hz) t ht)) hbudget
      change u (eR z) < L
      simpa only [eR, rescaledChart_apply, Complex.coe_smul] using hpoint
  let eL := openRestrictedChart M S hS eR
  have hsource1 : closedBall (0 : ComplexVector n) 1 ⊆ eL.source := by
    intro z hz
    have hz2 : z ∈ ball (0 : ComplexVector n) 2 := mem_ball.mpr
      ((mem_closedBall.mp hz).trans_lt (by norm_num))
    exact mem_targetRestriction_source eR S hS.nonempty.to_subtype (hsource2 hz2) (hcomp hz2)
  refine ⟨eL, ?_, hsource1, ?_, ?_⟩
  · apply Subtype.ext
    have hz0 : (0 : ComplexVector n) ∈ eL.source := hsource1 (mem_closedBall_self (by norm_num))
    exact (targetRestriction_value eR S hS.nonempty.to_subtype hz0).trans
      ((rescaledChart_center e z₀ ((c * δ : ℝ) : ℂ) hscale).trans hcenter)
  · exact targetRestriction_contMDiffOn eR S hS.nonempty.to_subtype heR
  · exact targetRestriction_inverse_contMDiffOn eR S hS.nonempty.to_subtype heiR

end Yau.NodeProofs.F01Aux
