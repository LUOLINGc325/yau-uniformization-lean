import Yau.Proofs.F01MetricEntryLog
import Yau.Proofs.F01ConformalRayleighContact
import Yau.Proofs.F01MixedWirtingerLinearity
import Yau.Proofs.F01ScalarChartSmooth

/-! The logarithmic actual fixed-direction Rayleigh quotient has the
diagonal logarithmic jet minus the actual conformal scalar jet at a normal point. -/
noncomputable section
open Set Filter
open scoped Manifold ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformal_rayleigh_log_wirt (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0)
    (a : Fin n) (v : ComplexVector n) :
    wirt (fun w => (Real.log (matrixRayleigh (pullbackMatrix (conformalField g f) e w)
      (pullbackMatrix k e w) (Pi.single a 1)) : ℂ)) 0 v =
        wirt (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 v -
          wirt (fun w => (f (e w) : ℂ)) 0 v := by
  have hqd := Complex.reCLM.contDiff.contDiffAt.comp 0 (pullbackMatrix_entry_contDiffAt k hk e he hs0 a a)
  have hgd := Complex.reCLM.contDiff.contDiffAt.comp 0 (pullbackMatrix_entry_contDiffAt g hg e he hs0 a a)
  have hqpos := pullback_diagonal_pos k e he hei hs0 a
  have hgpos := pullback_diagonal_pos g e he hei hs0 a
  have hLq : DifferentiableAt ℝ (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (hqd.log hqpos.ne')).differentiableAt (by simp)
  have hLg : DifferentiableAt ℝ (fun w => (Real.log (pullbackMatrix g e w a a).re : ℂ)) 0 :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (hgd.log hgpos.ne')).differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ (fun w => (f (e w) : ℂ)) 0 :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (smoothFn_comp_holomorphic_chart f hf e he)).contDiffAt
        (e.open_source.mem_nhds hs0)).differentiableAt (by simp)
  have hgerm : (fun w => (Real.log (matrixRayleigh (pullbackMatrix (conformalField g f) e w)
      (pullbackMatrix k e w) (Pi.single a 1)) : ℂ)) =ᶠ[𝓝 (0 : ComplexVector n)]
      (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ) - (f (e w) : ℂ) -
        (Real.log (pullbackMatrix g e w a a).re : ℂ)) := by
    filter_upwards [e.open_source.mem_nhds hs0] with w hw
    have hqp := pullback_diagonal_pos k e he hei hw a
    have hgp := pullback_diagonal_pos g e he hei hw a
    rw [matrixRayleigh_single, conformalField_pullbackMatrix]
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [Real.log_div hqp.ne' (mul_pos (Real.exp_pos _) hgp).ne',
      Real.log_mul (Real.exp_pos _).ne' hgp.ne', Real.log_exp]
    push_cast
    ring
  have hgw : wirt (fun w => pullbackMatrix g e w a a) 0 v = 0 := by
    unfold wirt
    rw [hjet a a]
    simp
  have hLgw : wirt (fun w => (Real.log (pullbackMatrix g e w a a).re : ℂ)) 0 v = 0 := by
    rw [pullback_diagonal_log_wirt g hg e he hei hs0 a v, hgw, mul_zero]
  rw [wirt_eq_of_eventuallyEq hgerm,
    wirt_sub_rule (fun w : ComplexVector n => (Real.log (pullbackMatrix k e w a a).re : ℂ) - (f (e w) : ℂ))
      (fun w : ComplexVector n => (Real.log (pullbackMatrix g e w a a).re : ℂ)) 0 v (hLq.sub hfd) hLg,
    wirt_sub_rule (fun w : ComplexVector n => (Real.log (pullbackMatrix k e w a a).re : ℂ))
      (fun w : ComplexVector n => (f (e w) : ℂ)) 0 v hLq hfd, hLgw, sub_zero]

end Yau.NodeProofs.F01Aux
