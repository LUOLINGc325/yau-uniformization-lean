import Yau.Proofs.F01RawRayleighHeatBound
import Yau.Proofs.F01RayleighGradientError
import Yau.Proofs.F01ConformalGradientTrace

/-! Cancellation of the actual negative square gives the paper's
Rayleigh drift inequality with the same intrinsic conformal budgets. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem rayleigh_drift_bound (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
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
    (hevolution : HasDerivAt qcurve
      (leviC (fun w => Real.log (pullbackMatrix k e w).det.re) 0 a a).re t) :
    deriv (fun s => Real.log (qcurve s / Real.exp (f (e 0)))) t -
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
  let g0 := openRestrictedField M S hS g.form
  have hg0 := openRestrictedField_metricSmooth M S hS
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)
  have hraw := raw_rayleigh_heat_bound M S hS g hcurv f u hf hu k hk t hpot e he hei hs0
    hvalue hjet values hdiag a B G hB hG hlarge hgrad hlo hhi qcurve hqt hevolution
  have hnegative := flow_negative_square_gradient_error g0 k hg0 hk f hf u hu t hpot
    e he hei hs0 hvalue hjet values hdiag a hlarge
  dsimp only at hnegative
  have htrace := conformal_normal_trace_nonneg g0 k f e he hei hs0 hvalue values hdiag
  have hdual := conformal_normal_gradient_le_trace g0 k f hf e he hei hs0 hvalue values hdiag
  have hbound : dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2
      (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i))) ≤
      G * traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g0 f) e 0) := by
    calc
      _ ≤ _ := hdual
      _ ≤ traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g0 f) e 0) * G :=
        mul_le_mul_of_nonneg_left hgrad htrace
      _ = _ := mul_comm _ _
  linarith

end Yau.NodeProofs.F01Aux
