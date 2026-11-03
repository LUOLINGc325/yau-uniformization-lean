import Yau.Proofs.C01SpatialBisectional

/-! Joint positivity implies nonnegative bisectional curvature of the
original flow at every positive time. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_nonnegBisectional_positive
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (t : ℝ) (ht : 0 < t) : NonnegBisectional (h t) := by
  intro x ξ η
  let w : ℂ := ((Real.log t / 2 : ℝ) : ℂ)
  have hw : Real.exp (2 * w.re) = t := by
    dsimp only [w]
    rw [Complex.ofReal_re]
    convert Real.exp_log ht using 1 <;> congr 1 <;> ring
  have hH (a b : Fin n) :
      ContDiffAt ℝ 2 (fun z => hMat (h t) x z a b) (chartPt x x) := by
    have hmap : ContDiffOn ℝ ∞ (fun z : ComplexVector n => (z, t)) (chartTarget x) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have hlocal := (metricFamily_hMat_contDiffOn hflow.1.2.1 x a b).comp hmap
      (fun z hz => ⟨hz, ht.le⟩)
    exact (hlocal.contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target (I := ComplexModel n) x))).of_le (by simp)
  have hcurve := localizedFlow_spacetime_curvature_nonneg hflow hjoint x
    (chartPt x x) η (mem_extChartAt_target (I := ComplexModel n) x) w 0
    (WithLp.ofLp ξ)
  have heq := spatial_line_curvature_eq_bisectional (h t) x ξ η hH
  dsimp only at heq
  rw [← heq]
  simpa only [spacetimeMetricLine, mul_zero, add_zero, hw] using hcurve

end Yau.NodeProofs.C01Aux
