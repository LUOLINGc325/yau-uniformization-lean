import Yau.Proofs.C03SheetSeed
import Yau.Proofs.C03RayleighDual

/-! The fixed target cutoff has a uniformly bounded genuine Dolbeault
vector and vanishes on its inner ball and outside its support. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L14Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem seedCutoffDbar_contDiff (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (seedCutoffDbar (n := n) δ hδ) := by
  apply (contDiff_piLp 2).mpr
  intro i
  apply wirtBar_contDiff
  exact Complex.ofRealCLM.contDiff.comp (seedCutoff δ hδ).contDiff

theorem seedCutoffDbar_eq_zero_of_cutoff_germ (δ : ℝ) (hδ : 0 < δ)
    (w : ComplexVector n) (b : ℝ)
    (hg : seedCutoff δ hδ =ᶠ[𝓝 w] fun _ => b) : seedCutoffDbar δ hδ w = 0 := by
  have hgc : (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ)) =ᶠ[𝓝 w] fun _ => (b : ℂ) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have hD : fderiv ℝ (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ)) w = 0 := by
    rw [hgc.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (b : ℂ) w).fderiv
  ext i
  change wirtBar (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ)) w (stdVec i) = 0
  simp only [wirtBar, hD, ContinuousLinearMap.zero_apply, mul_zero, add_zero]

theorem seedCutoffDbar_zero_inner (δ : ℝ) (hδ : 0 < δ)
    (w : ComplexVector n) (hw : w ∈ ball (0 : ComplexVector n) (δ / 2)) :
    seedCutoffDbar δ hδ w = 0 :=
  seedCutoffDbar_eq_zero_of_cutoff_germ δ hδ w 1
    ((seedCutoff δ hδ).eventuallyEq_one_of_mem_ball hw)

theorem seedCutoffDbar_zero_outside (δ : ℝ) (hδ : 0 < δ)
    (w : ComplexVector n) (hw : w ∉ closedBall (0 : ComplexVector n) δ) :
    seedCutoffDbar δ hδ w = 0 := by
  apply seedCutoffDbar_eq_zero_of_cutoff_germ δ hδ w 0
  apply notMem_tsupport_iff_eventuallyEq.mp
  rw [(seedCutoff δ hδ).tsupport_eq]
  exact hw

theorem exists_seedCutoffDbar_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : ℝ, 0 < G ∧ ∀ w : ComplexVector n, ‖seedCutoffDbar δ hδ w‖ ≤ G := by
  obtain ⟨G, hG⟩ := (isCompact_closedBall (0 : ComplexVector n) δ).exists_bound_of_continuousOn
    (seedCutoffDbar_contDiff δ hδ).continuous.continuousOn
  refine ⟨max 1 G, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro w
  by_cases hw : w ∈ closedBall (0 : ComplexVector n) δ
  · exact (hG w hw).trans (le_max_right _ _)
  · rw [seedCutoffDbar_zero_outside δ hδ w hw, norm_zero]
    exact zero_le_one.trans (le_max_left _ _)

theorem inverse_quadratic_le_of_matrix_lower (H : Herm n) (hH : H.PosDef)
    (d : ℝ) (hd : 0 < d) (hlo : HermLE ((d : ℂ) • (1 : Herm n)) H)
    (F : ComplexVector n) : ellipsoidQuadratic H⁻¹ F ≤ ‖F‖ ^ 2 / d := by
  let ξ : ComplexVector n := WithLp.toLp 2 (star (WithLp.ofLp F))
  have hbound := LogDual.dualSquared_le_of_lower (fun _ : ComplexVector n => H)
    (0 : ComplexVector n) ξ hH d hd hlo
  change dualNormMat H ξ ≤ ‖ξ‖ ^ 2 / d at hbound
  have hn : ‖ξ‖ = ‖F‖ := by
    simp only [ξ, EuclideanSpace.norm_eq, Pi.star_apply, norm_star]
  rw [hn] at hbound
  dsimp only [ξ] at hbound
  rw [Rayleigh.dualNormMat_conjugate] at hbound
  exact hbound

end Yau.Proofs.C03Aux
