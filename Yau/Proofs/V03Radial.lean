import Yau.Proofs.V03Elementary

/-! The radial map preserves the original closed-disc regularity, the center,
and the physical-time restrictions. Boundary wall and energy convergence are
proved separately from these structural facts. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem radial_maps_closedBall {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Set.MapsTo (fun ζ : ℂ => (r : ℂ) * ζ)
      (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  intro ζ hζ
  rw [Metric.mem_closedBall, dist_zero_right] at hζ ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_one₀ hr1 (norm_nonneg _) hζ

theorem cotangentDisc_radial {f : ℂ → CotangentPoint X.manifold}
    (hf : CotangentDisc f) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    CotangentDisc (fun ζ => f ((r : ℂ) * ζ)) := by
  have hg : ContDiff ℂ ∞ (fun ζ : ℂ => (r : ℂ) * ζ) := contDiff_const.mul contDiff_id
  have hmap := radial_maps_closedBall hr hr1
  refine ⟨hf.1.comp hg.contMDiff.contMDiffOn hmap, fun ζ hζ => ?_⟩
  exact (hf.2 ((r : ℂ) * ζ) (hmap hζ)).comp ζ
    (hg.contDiffAt.contDiffWithinAt) hmap

theorem clock_contDiff_radial {w : ℂ → ℂ}
    (hw : ContDiffOn ℂ ∞ w (Metric.closedBall 0 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ContDiffOn ℂ ∞ (fun ζ => w ((r : ℂ) * ζ)) (Metric.closedBall 0 1) :=
  hw.comp (contDiff_const.mul contDiff_id).contDiffOn (radial_maps_closedBall hr hr1)

theorem radial_structural {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    CotangentDisc (radialVariationDisc F r).f ∧
    ContDiffOn ℂ ∞ (radialVariationDisc F r).w (Metric.closedBall 0 1) ∧
    (radialVariationDisc F r).w 0 = 0 ∧
    0 < (radialVariationDisc F r).s ∧ (radialVariationDisc F r).s < d.T ∧
    InCotangentTimeChart d.chart ((radialVariationDisc F r).f 0)
      (radialVariationDisc F r).s (centerCylinder d) ∧
    (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, discTime (radialVariationDisc F r) ζ < d.T) ∧
    InitiallyExtendedVariationDisc (radialVariationDisc F r) := by
  obtain ⟨hf, hw, hw0, hs, hsT, hc, ht, _, _⟩ := hF
  refine ⟨cotangentDisc_radial hf hr.le hr1.le,
    clock_contDiff_radial hw hr.le hr1.le, ?_, hs, hsT, ?_, ?_,
    radial_initiallyExtended F hf hw hr hr1⟩
  · simpa only [radial_clock_center] using hw0
  · simpa [radialVariationDisc] using hc
  · intro ζ hζ
    exact ht ((r : ℂ) * ζ) (radial_maps_closedBall hr.le hr1.le hζ)

end Yau.Blueprint.V03Proof
