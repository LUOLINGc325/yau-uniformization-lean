import Yau.Proofs.F01LogQuotientLevi
import Yau.Proofs.F01ConformalRayleighContact
import Yau.Proofs.F01MetricEntryLog
import Yau.Proofs.F01ScalarChartSmooth

/-! Exact heat-operator decomposition for the actual fixed-direction
Rayleigh logarithm.  The denominator is differentiated as the actual scalar. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem rayleigh_log_heat_decomposition (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (a : Fin n)
    (qcurve : ℝ → ℝ) (t qdot : ℝ)
    (hqt : qcurve t = (pullbackMatrix k e 0 a a).re)
    (hcurve : HasDerivAt qcurve qdot t) :
    deriv (fun s => Real.log (qcurve s / Real.exp (f (e 0)))) t -
        traceWith (pullbackMatrix k e 0) (leviC (fun w => Real.log (matrixRayleigh
          (pullbackMatrix (conformalField g f) e w) (pullbackMatrix k e w) (Pi.single a 1))) 0) =
      (deriv (fun s => Real.log (qcurve s)) t -
        traceWith (pullbackMatrix k e 0) (leviC (fun w => Real.log (pullbackMatrix k e w a a).re) 0)) +
      traceWith (pullbackMatrix k e 0) (leviC (fun w => f (e w)) 0) +
      traceWith (pullbackMatrix k e 0) (leviC (fun w => Real.log (pullbackMatrix g e w a a).re) 0) := by
  have hqp : 0 < qcurve t := by rw [hqt]; exact pullback_diagonal_pos k e he hei hs0 a
  have htime : deriv (fun s => Real.log (qcurve s / Real.exp (f (e 0)))) t =
      deriv (fun s => Real.log (qcurve s)) t :=
    (log_quotient_curve_hasDerivAt hcurve hqp (Real.exp_pos _)).deriv.trans
      (hcurve.log hqp.ne').deriv.symm
  have hqd : ContDiffAt ℝ 2 (fun w => (pullbackMatrix k e w a a).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0
      ((pullbackMatrix_entry_contDiffAt k hk e he hs0 a a).of_le (by simp))
  have hrd : ContDiffAt ℝ 2 (fun w => (pullbackMatrix g e w a a).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0
      ((pullbackMatrix_entry_contDiffAt g hg e he hs0 a a).of_le (by simp))
  have hfd : ContDiffAt ℝ 2 (fun w => f (e w)) 0 :=
    ((smoothFn_comp_holomorphic_chart f hf e he).contDiffAt
      (e.open_source.mem_nhds hs0)).of_le (by simp)
  have hW : (fun w => Real.log (matrixRayleigh (pullbackMatrix (conformalField g f) e w)
      (pullbackMatrix k e w) (Pi.single a 1))) =
      (fun w => Real.log ((pullbackMatrix k e w a a).re /
        (Real.exp (f (e w)) * (pullbackMatrix g e w a a).re))) := by
    funext w
    rw [matrixRayleigh_single, conformalField_pullbackMatrix]
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hlevi := leviC_log_exp_quotient
    (fun w => (pullbackMatrix k e w a a).re) (fun w => f (e w))
    (fun w => (pullbackMatrix g e w a a).re) e.open_source
    (fun w hw => ⟨pullback_diagonal_pos k e he hei hw a,
      pullback_diagonal_pos g e he hei hw a⟩) hs0 hqd hfd hrd
  rw [htime, hW, hlevi, traceWith_sub, traceWith_sub]
  ring

end Yau.NodeProofs.F01Aux
