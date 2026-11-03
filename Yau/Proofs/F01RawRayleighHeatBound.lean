import Yau.Proofs.F01RayleighHeatDecomposition
import Yau.Proofs.F01LogDiagonalHeatIdentity
import Yau.Proofs.F01FlowSecondTraceBound
import Yau.Proofs.F01RestrictedDenominatorTrace

/-! The raw paper Rayleigh heat estimate on the actual approximating
component, obtained from the original matrix equation and computed normal jets. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem raw_rayleigh_heat_bound (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
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
      -(pullbackMatrix k e 0 a a).re⁻¹ *
        (∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ *
          Complex.normSq (wirt (fun w => pullbackMatrix k e w j i) 0 (stdVec a))) +
      dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2
        (fun i => wirt (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 (stdVec i))) +
      (3 * B + G) * traceWith (pullbackMatrix k e 0)
        (pullbackMatrix (conformalField (openRestrictedField M S hS g.form) f) e 0) := by
  let g0 := openRestrictedField M S hS g.form
  have hg0 := openRestrictedField_metricSmooth M S hS
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g)
  have hdec := rayleigh_log_heat_decomposition g0 k hg0 hk f hf e he hei hs0 a qcurve t
    (leviC (fun w => Real.log (pullbackMatrix k e w).det.re) 0 a a).re hqt hevolution
  have hheat := log_diagonal_heat_identity (pullbackMatrix k e) e.open_source
    (fun i j => pullbackMatrix_entry_contDiffOn k hk e he i j)
    (fun w hw => pullbackMatrix_posDef k e he hei hw) hs0 values hdiag a qcurve t hqt hevolution
  dsimp only at hheat
  have herror := conformal_flow_second_trace_bound M S hS g f u hf hu k hk t hpot e he hei hs0
    hvalue hjet values hdiag a B G hB hG hlarge hgrad hlo hhi
  have hbackground := restricted_normal_log_denominator_trace_nonpos M S hS g hcurv k e he hei
    hs0 hvalue hjet values hdiag a
  rw [hdec, hheat]
  linarith

end Yau.NodeProofs.F01Aux
