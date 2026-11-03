import Yau.Proofs.V03Walls
import Mathlib.Analysis.Complex.AbsMax

/-! The center normalization removes inner factors: a holomorphic comparison
with the same boundary modulus and center value determines the whole disc. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem norm_le_of_circle_bound {h : ℂ → ℂ}
    (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1)) {C : ℝ}
    (hC : ∀ θ, ‖h (circlePoint θ)‖ ≤ C) :
    ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ C := by
  have hd := hh.differentiableOn (by simp)
  intro ζ hζ
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
    (hd.diffContOnCl_ball Set.Subset.rfl) ?_ ?_
  · intro z hz
    have hz' : ‖z‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        Metric.frontier_ball_subset_sphere hz
    have he : circlePoint (Complex.arg z) = z := by
      simpa [circlePoint, hz'] using Complex.norm_mul_exp_arg_mul_I z
    simpa only [he] using hC (Complex.arg z)
  · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hζ

theorem holomorphic_eq_of_boundary_modulus_center {h H : ℂ → ℂ}
    (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1))
    (hH0 : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, H ζ ≠ 0)
    (hb : ∀ θ, ‖h (circlePoint θ)‖ = ‖H (circlePoint θ)‖)
    (hc : h 0 = H 0) :
    ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, h ζ = H ζ := by
  let R : ℂ → ℂ := fun ζ => h ζ / H ζ
  have hR : ContDiffOn ℂ ∞ R (Metric.closedBall 0 1) := hh.div hH hH0
  have hR0 : R 0 = 1 := by
    dsimp only [R]
    rw [hc, div_self (hH0 0 (by simp))]
  have hRb : ∀ θ, ‖R (circlePoint θ)‖ ≤ 1 := by
    intro θ
    simp only [R, norm_div, hb θ]
    exact le_of_eq (div_self (norm_ne_zero_iff.mpr (hH0 _ (circlePoint_mem_closedBall θ))))
  have hnorm := norm_le_of_circle_bound hR hRb
  have hmax : IsMaxOn (norm ∘ R) (Metric.ball (0 : ℂ) 1) 0 := by
    intro ζ hζ
    change ‖R ζ‖ ≤ ‖R 0‖
    rw [hR0, norm_one]
    exact hnorm ζ (Metric.ball_subset_closedBall hζ)
  have heq := Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0 : ℂ) 1).isPreconnected Metric.isOpen_ball
    ((hR.differentiableOn (by simp)).diffContOnCl_ball Set.Subset.rfl)
    (by simp : (0 : ℂ) ∈ Metric.ball 0 1) hmax
  intro ζ hζ
  have hζ' : ζ ∈ closure (Metric.ball (0 : ℂ) 1) := by
    simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hζ
  have hquot : h ζ / H ζ = 1 := by
    simpa only [Function.const_apply, hR0] using heq hζ'
  exact (div_eq_one_iff_eq (hH0 ζ hζ)).mp hquot

theorem outerCenter_pos (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) :
    0 < outerCenter d j a F := Real.exp_pos _

theorem realized_h_center (d : VariationData X q) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz r) :
    h 0 = (outerCenter d j a F : ℂ) := by
  apply Complex.ext
  · exact hR.2.2.2.2.2.2.1
  · exact hR.2.2.2.2.2.1

theorem realized_h_norm_le_one (d : VariationData X q) (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz r) :
    ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ 1 := by
  apply norm_le_of_circle_bound hR.2.2.2.1
  intro θ
  rw [hR.2.2.2.2.2.2.2.1 θ]
  exact (admissible_wallPower_bounds hd hF a θ).2

end Yau.Blueprint.V03Proof
