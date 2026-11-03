import Yau.LeafProofs.L23LocalDistanceSupportEnergyLaplacianTraceRegularity
import Yau.LeafProofs.L23DistanceEnergyHessian

/-! The physical Laplacian is the exact orthonormal trace of the same endpoint-energy rays. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

theorem realLap_eq_endpointParameter_secondDeriv_sum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : HermitianField M) (y : M.Carrier) (E : M.Carrier → ℝ) (Eu : ComplexVector n → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (hEu : Set.EqOn Eu (fun v => E (e v)) e.source)
    (hE : ContDiffAt ℝ 2 (inChart y E) (chartPt y y))
    (hc : ∀ w : ComplexVector n, ContDiffAt ℝ 2 (fun r : ℝ => chartPt y (e (r • w))) 0)
    (hv : ∀ w : ComplexVector n, HasDerivAt (fun r : ℝ => chartPt y (e (r • w))) w 0)
    (ha : ∀ w : ComplexVector n, HasDerivAt (deriv (fun r : ℝ => chartPt y (e (r • w))))
      (-chartChristoffelBilin h y (chartPt y y) w w) 0)
    (b : letI := underlyingRealTangentNormedAddCommGroup h y
      letI := underlyingRealTangentInnerProductSpace h y
      OrthonormalBasis κ ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y)) :
    realLap h E y = ∑ i, deriv (deriv (fun r : ℝ => Eu (r • realTangentCoords y y (b i)))) 0 := by
  rw [realLap,chartRealLaplacian_eq_orthonormal_covHessian h y hE b]
  apply Finset.sum_congr rfl
  intro i hi
  let w := realTangentCoords y y (b i)
  have HH := endpointRay_covariantHessian h y E e h0 he0 hE w (hc w) (hv w) (ha w)
  rw [chartCovHessianBilin_apply] at HH
  have HR : (fun r : ℝ => Eu (r • w)) =ᶠ[𝓝 (0 : ℝ)] (fun r : ℝ => E (e (r • w))) := by
    have HC : ContinuousAt (fun r : ℝ => r • w) 0 := (continuous_id.smul continuous_const).continuousAt
    have HU : ∀ᶠ r in 𝓝 (0 : ℝ), r • w ∈ e.source := HC.preimage_mem_nhds
      (by change e.source ∈ 𝓝 ((0 : ℝ) • w); rw [zero_smul]; exact e.open_source.mem_nhds h0)
    filter_upwards [HU] with r hr
    exact hEu hr
  exact HH.symm.trans HR.deriv.deriv_eq.symm

theorem realLap_endpointVariation_fieldPathEnergy_eq_secondDeriv_sum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : HermitianField M) (hh : MetricSmooth h) (y : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hL : L = realFrameCLM y y) (hend : ∀ v ∈ e.source, A 1 v = e v)
    (hfirst : HasFDerivAt (fun v => chartPt y (A 1 v)) ((realTangentCoords y y).comp L) 0)
    (hsecond : ∀ w : ComplexVector n, HasDerivAt (deriv (fun r : ℝ => chartPt y (A 1 (r • w))))
      (-chartChristoffelBilin h y (chartPt y y) (realTangentCoords y y (L w)) (realTangentCoords y y (L w))) 0)
    (b : letI := underlyingRealTangentNormedAddCommGroup h y
      letI := underlyingRealTangentInnerProductSpace h y
      OrthonormalBasis κ ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y)) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target →
    realLap h (fun z => fieldPathEnergy h (fun u => A u (e.symm z))) y =
      ∑ i, deriv (deriv (fun r : ℝ => fieldPathEnergy h
        (fun u => A u (r • realTangentCoords y y (b i))))) 0 := by
  letI := manifold_realSmooth M
  intro hA hinv
  let E := fun z : M.Carrier => fieldPathEnergy h (fun u => A u (e.symm z))
  let Eu := fun v : ComplexVector n => fieldPathEnergy h (fun u => A u v)
  have HEu : Set.EqOn Eu (fun v => E (e v)) e.source := by
    intro v hv
    change fieldPathEnergy h (fun u => A u v) = fieldPathEnergy h (fun u => A u (e.symm (e v)))
    rw [e.left_inv hv]
  have HE := (endpointVariation_staticEnergy_contDiffAt_two h hh y e A δ hδ h0 he0 hA hinv).2
  have Hecoord := endpointChart_contDiffAt_three_of_terminalVariation y e A δ hδ h0 he0 hend hA
  have HDe := endpointChart_hasFDerivAt_id y e (fun v => A 1 v) h0 L hL (fun v hv => hend v hv) hfirst
  have HC (w : ComplexVector n) : ContDiffAt ℝ 2 (fun r : ℝ => chartPt y (e (r • w))) 0 := by
    have HF : ContDiffAt ℝ 2 (fun v => chartPt y (e v)) ((0 : ℝ) • w) := by
      simpa only [zero_smul] using Hecoord.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)
    have HL : ContDiffAt ℝ 2 (fun r : ℝ => r • w) 0 := contDiffAt_id.smul_const w
    exact HF.comp (f := fun r : ℝ => r • w) (g := fun v => chartPt y (e v)) 0 HL
  exact realLap_eq_endpointParameter_secondDeriv_sum h y E Eu e h0 he0 HEu HE HC
    (endpointRay_hasDerivAt y e HDe)
    (endpointRay_secondJet_of_terminalVariation h y e (fun v => A 1 v) h0 L hL (fun v hv => hend v hv) hsecond) b

end Yau.LeafProofs.L23Aux
