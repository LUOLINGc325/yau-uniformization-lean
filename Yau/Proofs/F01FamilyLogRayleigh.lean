import Yau.Proofs.F01FamilyRayleighSmooth
import Yau.Proofs.F01ConformalRayleighContact
import Yau.Proofs.F01WithinAffineTime
import Yau.Proofs.F01MetricEntryLog

/-! The actual positive fixed-coordinate logarithmic Rayleigh test is
smooth on the full closed time set. Its one-sided time jet is computed
directly from the actual diagonal entry of the evolving metric. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_fixed_log_rayleigh_contDiffOn (g : HermitianField M)
    (hg : MetricSmooth g) (k : ℝ → HermitianField M) {I : Set ℝ}
    (hk : MetricFamilySmooth k I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {v : Fin n → ℂ} (hv : v ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      Real.log (matrixRayleigh (pullbackMatrix g e p.1) (pullbackMatrix (k p.2) e p.1) v))
      (e.source ×ˢ I) := by
  apply (metricFamily_fixed_rayleigh_contDiffOn g hg k hk e he hei hv).log
  intro p hp
  exact (div_pos (matrixQuadraticValue_pos (pullbackMatrix_posDef (k p.2) e he hei hp.1) hv)
    (matrixQuadraticValue_pos (pullbackMatrix_posDef g e he hei hp.1) hv)).ne'

theorem conformal_single_logRayleigh_time_eq (g : HermitianField M) (f : M.Carrier → ℝ)
    (k : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hvalue : pullbackMatrix g e 0 = 1) (j : Fin n) :
    (fun t => Real.log (matrixRayleigh (pullbackMatrix (conformalField g f) e 0)
      (pullbackMatrix (k t) e 0) (Pi.single j 1))) =
    (fun t => Real.log ((pullbackMatrix (k t) e 0 j j).re / Real.exp (f (e 0)))) := by
  funext t
  rw [matrixRayleigh_single, conformalField_pullbackMatrix, hvalue]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, Complex.ofReal_re]

theorem conformal_single_logRayleigh_hasDerivWithinAt
    (g : HermitianField M) (f : M.Carrier → ℝ) (k : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix g e 0 = 1) (j : Fin n) {I : Set ℝ} {t qdot : ℝ}
    (hq : HasDerivWithinAt (fun s => (pullbackMatrix (k s) e 0 j j).re) qdot I t) :
    HasDerivWithinAt (fun s => Real.log (matrixRayleigh (pullbackMatrix (conformalField g f) e 0)
      (pullbackMatrix (k s) e 0) (Pi.single j 1)))
      (qdot / (pullbackMatrix (k t) e 0 j j).re) I t := by
  rw [conformal_single_logRayleigh_time_eq g f k e hvalue j]
  exact log_quotient_curve_hasDerivWithinAt hq
    (pullback_diagonal_pos (k t) e he hei hs j) (Real.exp_pos _)

end Yau.NodeProofs.F01Aux
