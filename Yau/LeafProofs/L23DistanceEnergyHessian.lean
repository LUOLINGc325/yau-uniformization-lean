import Yau.LeafProofs.L23DistanceEnergyParameterJets
import Yau.LeafProofs.L23DistanceEnergyDirections

/-! Genuine normal-ray second derivatives are the original covariant Hessian. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem scalar_secondDeriv_comp_curve (f : V → ℝ) (c : ℝ → V) (r : ℝ)
    (hf : ContDiffAt ℝ 2 f (c r)) (hc : ContDiffAt ℝ 2 c r) (v a : V)
    (hv : HasDerivAt c v r) (ha : HasDerivAt (deriv c) a r) :
    deriv (deriv (fun s => f (c s))) r=fderiv ℝ (fderiv ℝ f) (c r) v v+fderiv ℝ f (c r) a := by
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) (c r) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have H := (hDf.hasFDerivAt.comp_hasDerivAt r hv).clm_apply ha
  change HasDerivAt (fun s => fderiv ℝ f (c s) (deriv c s))
    (fderiv ℝ (fderiv ℝ f) (c r) v (deriv c r)+fderiv ℝ f (c r) a) r at H
  have heq : deriv (fun s => f (c s))=ᶠ[𝓝 r]
      (fun s => fderiv ℝ f (c s) (deriv c s)) := by
    filter_upwards [hc.eventually (by norm_num),hc.continuousAt.preimage_mem_nhds
      (hf.eventually (by norm_num))] with s hsc hsf
    have hsf' : ContDiffAt ℝ 2 f (c s) := hsf
    exact ((hsf'.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      (hsc.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [heq.deriv_eq,H.deriv,hv.deriv]

variable {n : ℕ} {M : ComplexManifold n}

theorem scalar_normalRay_secondDeriv (h : HermitianField M) (y : M.Carrier)
    (f : ComplexVector n → ℝ) (c : ℝ → ComplexVector n)
    (hc0 : c 0=chartPt y y) (hf : ContDiffAt ℝ 2 f (chartPt y y))
    (hc : ContDiffAt ℝ 2 c 0) (w : ComplexVector n) (hv : HasDerivAt c w 0)
    (ha : HasDerivAt (deriv c) (-chartChristoffelBilin h y (chartPt y y) w w) 0) :
    deriv (deriv (fun r => f (c r))) 0=chartCovHessianBilin h y f (chartPt y y) w w := by
  have hf' : ContDiffAt ℝ 2 f (c 0) := hc0.symm ▸ hf
  rw [scalar_secondDeriv_comp_curve f c 0 hf' hc w _ hv ha,hc0,chartCovHessianBilin_apply,map_neg]
  ring

theorem endpointRay_covariantHessian (h : HermitianField M) (y : M.Carrier)
    (E : M.Carrier → ℝ) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hzero : (0 : ComplexVector n)∈e.source) (he0 : e 0=y)
    (hE : ContDiffAt ℝ 2 (inChart y E) (chartPt y y))
    (w : ComplexVector n)
    (hc : ContDiffAt ℝ 2 (fun r : ℝ => chartPt y (e (r • w))) 0)
    (hv : HasDerivAt (fun r : ℝ => chartPt y (e (r • w))) w 0)
    (ha : HasDerivAt (deriv (fun r : ℝ => chartPt y (e (r • w))))
      (-chartChristoffelBilin h y (chartPt y y) w w) 0) :
    deriv (deriv (fun r : ℝ => E (e (r • w)))) 0=
      chartCovHessianBilin h y (inChart y E) (chartPt y y) w w := by
  have helin : ContinuousAt (fun r : ℝ => r • w) 0 := by fun_prop
  have hecont0 : ContinuousAt (fun v : ComplexVector n => e v) ((0 : ℝ) • w) := by
    simpa only [zero_smul] using e.continuousOn.continuousAt (e.open_source.mem_nhds hzero)
  have hecont : ContinuousAt (fun r : ℝ => e (r • w)) 0 :=
    hecont0.comp (f := fun r : ℝ => r • w) helin
  have hsource : ∀ᶠ r in 𝓝 (0 : ℝ), e (r • w) ∈ (extChartAt (ComplexModel n) y).source := by
    apply hecont.preimage_mem_nhds
    simpa only [zero_smul,he0] using extChartAt_source_mem_nhds (I := ComplexModel n) y
  have heq : (fun r : ℝ => E (e (r • w)))=ᶠ[𝓝 (0 : ℝ)]
      (fun r => inChart y E (chartPt y (e (r • w)))) := by
    filter_upwards [hsource] with r hr
    exact (congrArg E ((extChartAt (ComplexModel n) y).left_inv hr)).symm
  rw [heq.deriv.deriv_eq]
  apply scalar_normalRay_secondDeriv h y (inChart y E) _ _ hE hc w hv ha
  simp only [zero_smul,he0]

end Yau.LeafProofs.L23Aux
