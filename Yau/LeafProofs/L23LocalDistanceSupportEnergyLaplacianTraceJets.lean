import Yau.LeafProofs.L23LocalDistanceSupportEnergyTime

/-! Genuine endpoint rays and energy germs for the physical Laplacian trace. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem endpointChart_contDiffAt_three_of_terminalVariation
    (y : M.Carrier) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (hend : ∀ v ∈ e.source, A 1 v = e v) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContDiffAt ℝ 3 (fun v => chartPt y (e v)) 0 := by
  letI := manifold_realSmooth M
  intro hA
  have h1 : (1 : ℝ) ∈ Set.Ioo (-δ) (1+δ) := by constructor <;> linarith
  have HA := (hA (1,0) ⟨h1,h0⟩).contMDiffAt ((isOpen_Ioo.prod e.open_source).mem_nhds ⟨h1,h0⟩)
  have HM : ContMDiffAt 𝓘(ℝ, ComplexVector n) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun v : ComplexVector n => ((1 : ℝ),v)) 0 := contMDiffAt_const.prodMk contMDiffAt_id
  have HF : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (fun v => A 1 v) 0 := HA.comp 0 HM
  have Hpoint : A 1 0 = y := (hend 0 h0).trans he0
  have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (chartPt y) (A 1 0) := by
    rw [Hpoint]
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3) (x := y) (x' := y) (mem_chart_source _ _)) using 1
  apply (HC.comp 0 HF).contDiffAt.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds h0] with v hv
  exact congrArg (chartPt y) (hend v hv).symm

theorem endpointRay_hasDerivAt
    (y : M.Carrier) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hDe : HasFDerivAt (fun v => chartPt y (e v)) (ContinuousLinearMap.id ℝ (ComplexVector n)) 0)
    (w : ComplexVector n) : HasDerivAt (fun r : ℝ => chartPt y (e (r • w))) w 0 := by
  have HL : HasDerivAt (fun r : ℝ => r • w) w 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have HF : HasFDerivAt (fun v => chartPt y (e v)) (ContinuousLinearMap.id ℝ (ComplexVector n)) ((0 : ℝ) • w) := by
    simpa only [zero_smul] using hDe
  convert! HF.comp_hasDerivAt 0 HL using 1

theorem endpointRay_secondJet_of_terminalVariation
    (h : HermitianField M) (y : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (F : ComplexVector n → M.Carrier) (h0 : (0 : ComplexVector n) ∈ e.source)
    (L : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (hL : L = realFrameCLM y y) (hend : Set.EqOn F e e.source)
    (hsecond : ∀ w : ComplexVector n, HasDerivAt (deriv (fun r : ℝ => chartPt y (F (r • w))))
      (-chartChristoffelBilin h y (chartPt y y) (realTangentCoords y y (L w)) (realTangentCoords y y (L w))) 0)
    (w : ComplexVector n) :
    HasDerivAt (deriv (fun r : ℝ => chartPt y (e (r • w))))
      (-chartChristoffelBilin h y (chartPt y y) w w) 0 := by
  have H := hsecond w
  rw [hL,realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _)] at H
  have Hnear : (fun r : ℝ => chartPt y (e (r • w))) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => chartPt y (F (r • w))) := by
    have HR : ContinuousAt (fun r : ℝ => r • w) 0 := (continuous_id.smul continuous_const).continuousAt
    have HU : ∀ᶠ r in 𝓝 (0 : ℝ), r • w ∈ e.source := HR.preimage_mem_nhds
      (by change e.source ∈ 𝓝 ((0 : ℝ) • w); rw [zero_smul]; exact e.open_source.mem_nhds h0)
    filter_upwards [HU] with r hr
    exact congrArg (chartPt y) (hend hr).symm
  exact H.congr_of_eventuallyEq Hnear.deriv

theorem endpointEnergy_parameter_eventuallyEq_inChart
    (y : M.Carrier) (E : M.Carrier → ℝ) (Eu : ComplexVector n → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (hEu : Set.EqOn Eu (fun v => E (e v)) e.source) :
    Eu =ᶠ[𝓝 (0 : ComplexVector n)] (fun v => inChart y E (chartPt y (e v))) := by
  have Hsource : ∀ᶠ v in 𝓝 (0 : ComplexVector n), e v ∈ (extChartAt (ComplexModel n) y).source :=
    (e.continuousAt h0).preimage_mem_nhds (by rw [he0]; exact
      (isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds (mem_extChartAt_source y))
  filter_upwards [e.open_source.mem_nhds h0,Hsource] with v hv hvs
  rw [hEu hv]
  change E (e v) = E (chartInv y (chartPt y (e v)))
  exact congrArg E ((extChartAt (ComplexModel n) y).left_inv hvs).symm

theorem endpointEnergy_ray_secondDeriv_eq_inChart
    (y : M.Carrier) (E : M.Carrier → ℝ) (Eu : ComplexVector n → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = y)
    (hEu : Set.EqOn Eu (fun v => E (e v)) e.source) (w : ComplexVector n) :
    deriv (deriv (fun r : ℝ => Eu (r • w))) 0 =
      deriv (deriv (fun r : ℝ => inChart y E (chartPt y (e (r • w))))) 0 := by
  have HE := endpointEnergy_parameter_eventuallyEq_inChart y E Eu e h0 he0 hEu
  have HR : Tendsto (fun r : ℝ => r • w) (𝓝 0) (𝓝 0) := by
    have H : ContinuousAt (fun r : ℝ => r • w) 0 := (continuous_id.smul continuous_const).continuousAt
    change Tendsto (fun r : ℝ => r • w) (𝓝 0) (𝓝 ((0 : ℝ) • w)) at H
    simpa only [zero_smul] using H
  exact (HE.comp_tendsto HR).deriv.deriv_eq

end Yau.LeafProofs.L23Aux
