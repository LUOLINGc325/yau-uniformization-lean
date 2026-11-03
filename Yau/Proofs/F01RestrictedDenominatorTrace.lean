import Yau.Proofs.F01RestrictedNormalCurvatureSign
import Yau.Proofs.F01LogQuotientLevi
import Yau.Proofs.F01LogLaplacianDiagonal
import Yau.Proofs.F01MetricEntryLog
import Yau.Proofs.F01OpenMetricSmooth

/-! The actual logarithmic background denominator contributes a
nonpositive trace on the open component, inherited from the ambient curvature. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem restricted_normal_log_denominator_trace_nonpos (g : SmoothMetric M)
    (hcurv : NonnegBisectional g.form)
    (k : HermitianField (openConnectedManifold M S hS))
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hzero : ∀ a b, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w a b) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) (a : Fin n) :
    traceWith (pullbackMatrix k e 0) (leviC (fun w => Real.log
      (pullbackMatrix (openRestrictedField M S hS g.form) e w a a).re) 0) ≤ 0 := by
  let g0 := openRestrictedField M S hS g.form
  have hg0 := openRestrictedField_metricSmooth M S hS
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)
  have hentry : ContDiffAt ℝ ∞ (fun w => pullbackMatrix g0 e w a a) 0 :=
    pullbackMatrix_entry_contDiffAt g0 hg0 e he hs0 a a
  have hr : ContDiffAt ℝ 2 (fun w => (pullbackMatrix g0 e w a a).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hentry.of_le (by simp))
  have hrvalue : (pullbackMatrix g0 e 0 a a).re = 1 := by rw [hvalue]; simp
  have hrzero : fderiv ℝ (fun w => (pullbackMatrix g0 e w a a).re) 0 = 0 := by
    change fderiv ℝ (Complex.reCLM ∘ (fun w => pullbackMatrix g0 e w a a)) 0 = _
    rw [fderiv_comp 0 Complex.reCLM.differentiableAt
      (hentry.differentiableAt (by simp)), ContinuousLinearMap.fderiv, hzero a a]
    simp
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  rw [hdiag, traceWith_real_diagonal values (fun i => (hv i).ne')]
  apply Finset.sum_nonpos
  intro i hi
  rw [leviC_log_normal_diagonal hr hrvalue hrzero]
  have hm := mixed_wirtinger_eq_of_eqOn e.open_source
    (show EqOn (fun w => (((pullbackMatrix g0 e w a a).re : ℝ) : ℂ))
      (fun w => pullbackMatrix g0 e w a a) e.source from
        fun w _ => pullback_diagonal_real g0 e w a) hs0 (stdVec i) (stdVec i)
  have hs := restricted_normal_metric_mixed_nonpos M S hS g hcurv e he hei hs0 hzero i a
  have hmix : (leviC (fun w => (pullbackMatrix g0 e w a a).re) 0 i i).re ≤ 0 := by
    change (wirt (fun w => wirtBar
      (fun y => (((pullbackMatrix g0 e y a a).re : ℝ) : ℂ)) w (stdVec i)) 0 (stdVec i)).re ≤ 0
    rw [hm]
    exact hs
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hv i).le) hmix

end Yau.NodeProofs.F01Aux
