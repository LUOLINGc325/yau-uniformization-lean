import Yau.Proofs.F01RayleighDriftBound
import Yau.Proofs.F01WithinAffineTime

/-! The actual Rayleigh drift estimate on the original closed time set.
Only an actual one-sided metric time jet is needed; the affine comparison
curve reuses the previously computed spatial identity without new hypotheses. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem rayleigh_drift_bound_within (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
    (f u : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f) (hu : SmoothFn u)
    (k : HermitianField (openConnectedManifold M S hS)) (hk : MetricSmooth k) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField (openRestrictedField M S hS g.form) f) x -
      (t : ℂ) • ricci (conformalField (openRestrictedField M S hS g.form) f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w i j) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)))
    (a : Fin n) (B G : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hlarge : Real.exp (f (e 0)) ≤ (pullbackMatrix k e 0 a a).re)
    (hgrad : gradNormSq (conformalField (openRestrictedField M S hS g.form) f) f (e 0) ≤ G)
    (hlo : (levi f (e 0) - ((-B : ℝ) : ℂ) •
      gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0) -
      levi f (e 0)).PosSemidef)
    (qcurve : ℝ → ℝ) (hqt : qcurve t = (pullbackMatrix k e 0 a a).re)
    {I : Set ℝ} (hUnique : UniqueDiffWithinAt ℝ I t)
    (hevolution : HasDerivWithinAt qcurve
      (leviC (fun w => Real.log (pullbackMatrix k e w).det.re) 0 a a).re I t) :
    derivWithin (fun s => Real.log (qcurve s / Real.exp (f (e 0)))) I t -
        traceWith (pullbackMatrix k e 0) (leviC (fun w => Real.log (matrixRayleigh
          (pullbackMatrix (conformalField (openRestrictedField M S hS g.form) f) e w)
          (pullbackMatrix k e w) (Pi.single a 1))) 0) ≤
      (3 * B + 3 * G) * traceWith (pullbackMatrix k e 0)
        (pullbackMatrix (conformalField (openRestrictedField M S hS g.form) f) e 0) +
      2 * (Real.exp (f (e 0)) / (pullbackMatrix k e 0 a a).re) *
        Real.sqrt (dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 (fun i => wirt
          (fun w => (Real.log (matrixRayleigh
            (pullbackMatrix (conformalField (openRestrictedField M S hS g.form) f) e w)
            (pullbackMatrix k e w) (Pi.single a 1)) : ℂ)) 0 (stdVec i)))) *
        Real.sqrt (dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2
          (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)))) := by
  have hqpos : 0 < qcurve t := by
    rw [hqt]
    exact pullback_diagonal_pos k e he hei hs0 a
  rw [log_quotient_derivWithin_eq_affine_deriv hUnique hevolution hqpos (Real.exp_pos _)]
  exact rayleigh_drift_bound M S hS g hcurv f u hf hu k hk t hpot e he hei hs0
    hvalue hjet values hdiag a B G hB hG hlarge hgrad hlo hhi
    (affineTimeCurve (qcurve t)
      (leviC (fun w => Real.log (pullbackMatrix k e w).det.re) 0 a a).re t)
    ((affineTimeCurve_self _ _ _).trans hqt) (affineTimeCurve_hasDerivAt _ _ _)

end Yau.NodeProofs.F01Aux
