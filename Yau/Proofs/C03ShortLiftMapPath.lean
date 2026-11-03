import Yau.Proofs.C03ShortLiftRadial
import Yau.Geometry.Flat

/-! Push actual source curves through the original local map, with legal endpoint extensions. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set Filter
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint C07RadialCurveAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}
local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))

theorem euclidean_curve_contDiffAt (hn : 1 ≤ n) {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    {t : ℝ} (ht : t ∉ gamma.breakpoints) :
    ContDiffAt ℝ 1 (gamma : ℝ → ComplexVector n) t := by
  have H := gamma.piecewise_c1 t ht
  change ContDiffAt ℝ 1
    (fun s => extChartAt (ComplexModel n) (gamma t : ComplexVector n) (gamma s)) t at H
  rw [extChartAt_model_space_eq_id] at H
  exact H

theorem euclidean_curve_velocity (hn : 1 ≤ n) {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b) (t : ℝ) :
    realTangentDerivative gamma t = deriv (gamma : ℝ → ComplexVector n) t := by
  change chartVec (gamma t) (gamma t)
    (fderiv ℝ (fun s => chartPt (gamma t) (gamma s)) t 1) = _
  rw [chartVec_euclidean]
  change fderiv ℝ
    (fun s => extChartAt (ComplexModel n) (gamma t : ComplexVector n) (gamma s)) t 1 = _
  rw [extChartAt_model_space_eq_id]
  exact fderiv_apply_one_eq_deriv

def mappedPath (Phi : ComplexVector n → M.Carrier) (hn : 1 ≤ n)
    {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b) (t : ℝ) :
    M.Carrier := Phi (gamma (radialClamp t))

theorem mappedPath_piecewise_c1 {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r)
    {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htb : t ∉ gamma.breakpoints) :
    ContDiffAt ℝ 1 (fun s => chartPt (mappedPath Phi hn gamma t)
      (mappedPath Phi hn gamma s)) t := by
  by_cases ht : t < 0
  · apply (contDiffAt_const (c := chartPt (mappedPath Phi hn gamma t) (Phi (gamma 0)))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [mappedPath, radialClamp_of_neg hs]
  · by_cases ht' : 1 < t
    · apply (contDiffAt_const (c := chartPt (mappedPath Phi hn gamma t) (Phi (gamma 1)))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht'] with s hs
      simp only [mappedPath, radialClamp_of_gt_one hs]
    · have hti : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (le_of_not_gt ht) ht0.symm, lt_of_le_of_ne (le_of_not_gt ht') ht1⟩
      have hpt : mappedPath Phi hn gamma t = Phi (gamma t) := by
        simp only [mappedPath, radialClamp_eq ⟨hti.1.le, hti.2.le⟩]
      let G : ComplexVector n → ComplexVector n := fun z => chartPt (Phi (gamma t)) (Phi z)
      have hG : ContDiffAt ℂ ∞ G (gamma t) :=
        (contMDiffAt_extChartAt.comp (gamma t)
          (hPhi.contMDiffAt (Metric.isOpen_ball.mem_nhds (hmem t ⟨hti.1.le, hti.2.le⟩)))).contDiffAt
      have H := (((hG.restrict_scalars ℝ).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp t
        (euclidean_curve_contDiffAt hn gamma htb))
      apply H.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
      rw [hpt]
      simp only [mappedPath, radialClamp_eq ⟨hs.1.le, hs.2.le⟩]
      rfl

def mappedCurve {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r) :
    PiecewiseC1Curve (Phi a) (Phi b) where
  toFun := mappedPath Phi hn gamma
  start_eq := by simp only [mappedPath, radialClamp, min_eq_right zero_le_one,
    max_self, gamma.start_eq]
  finish_eq := by simp only [mappedPath, radialClamp, min_self,
    max_eq_right zero_le_one, gamma.finish_eq]
  breakpoints := gamma.breakpoints ∪ {0, 1}
  breakpoints_mem := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact gamma.breakpoints_mem t ht
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> norm_num
  continuous_on := by
    apply (hPhi.continuousOn.comp gamma.continuous_on hmem).congr
    intro t ht
    simp only [mappedPath, radialClamp_eq ht, Function.comp_apply]
  piecewise_c1 := by
    intro t ht
    have ht' : t ∉ gamma.breakpoints ∧ t ≠ 0 ∧ t ≠ 1 := by
      simpa only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] using ht
    exact mappedPath_piecewise_c1 hPhi hn gamma hmem ht'.2.1 ht'.2.2 ht'.1

theorem mappedCurve_on_interval {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    mappedCurve hPhi hn gamma hmem t = Phi (gamma t) := by
  exact congrArg (fun s => Phi (gamma s)) (radialClamp_eq ht)

end Yau.Proofs.C03Aux.ShortLift

