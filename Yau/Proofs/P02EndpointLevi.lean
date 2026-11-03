import Yau.Proofs.P02EnergyPair
import Yau.LeafProofs.L23LocalDistanceSupportEnergyMajorant
import Yau.LeafProofs.L23LocalDistanceSupportEnergyLaplacianTraceJets
import Yau.LeafProofs.L23DistanceEnergyHessian
import Yau.LeafProofs.L22LeviBasic

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract L22Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem covariant_pair_eq_levi (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h) (y : M.Carrier)
    (f : ComplexVector n → ℝ) (w : ComplexVector n) :
    chartCovHessianBilin h y f (chartPt y y) w w +
      chartCovHessianBilin h y f (chartPt y y) (Complex.I • w) (Complex.I • w) =
      4 * complexLeviQuadratic f (chartPt y y) w := by
  have hII : chartChristoffelBilin h y (chartPt y y) (Complex.I • w) (Complex.I • w) =
      -chartChristoffelBilin h y (chartPt y y) w w :=
    chartChristoffelBilin_I_I h hs hk y (z := chartPt y y) (mem_extChartAt_target y) w
  rw [chartCovHessianBilin_apply, chartCovHessianBilin_apply, hII, map_neg]
  unfold complexLeviQuadratic
  ring

theorem parallel_parameter_pair_eq_levi (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier)
    (H : ParallelVariationData h γ δ e P A)
    (E : M.Carrier → ℝ) (Eu : ComplexVector n → ℝ)
    (hEu : Set.EqOn Eu (fun v => E (e v)) e.source)
    (hE : ContDiffAt ℝ 2 (inChart (γ 1) E) (chartPt (γ 1) (γ 1)))
    (w : ComplexVector n) :
    deriv (deriv (fun r : ℝ => Eu (r • w))) 0 +
      deriv (deriv (fun r : ℝ => Eu (r • (Complex.I • w)))) 0 =
      4 * complexLeviQuadratic (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) w := by
  letI := manifold_realSmooth M
  have h1 : (1 : ℝ) ∈ Set.Ioo (-δ) (1+δ) := by
    constructor <;> linarith [H.delta_pos]
  have hc : γ 1 ∈ (extChartAt (ComplexModel n) (γ 1)).source := mem_extChartAt_source _
  have hDe : HasFDerivAt (fun v => chartPt (γ 1) (e v))
      (ContinuousLinearMap.id ℝ (ComplexVector n)) 0 := by
    have HD := (H.jets (γ 1) 1 h1 hc).2.1
    rw [one_smul, H.terminal_frame] at HD
    have hcomp : (realTangentCoords (γ 1) (γ 1)).comp (realFrameCLM (γ 1) (γ 1)) =
        ContinuousLinearMap.id ℝ (ComplexVector n) := by
      apply ContinuousLinearMap.ext
      intro v
      exact realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _) v
    rw [hcomp] at HD
    apply HD.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds H.zero_source] with v hv
    exact congrArg (chartPt (γ 1)) (H.endpoints v hv).2.symm
  have hchart : ContDiffAt ℝ 3 (fun v => chartPt (γ 1) (e v)) 0 :=
    endpointChart_contDiffAt_three_of_terminalVariation (γ 1) e A δ H.delta_pos
      H.zero_source H.endpoint_zero (fun v hv => (H.endpoints v hv).2) H.smooth
  have hscalar (v : ComplexVector n) :
      deriv (deriv (fun r : ℝ => Eu (r • v))) 0 =
        chartCovHessianBilin h (γ 1) (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) v v := by
    rw [endpointEnergy_ray_secondDeriv_eq_inChart (γ 1) E Eu e H.zero_source
      H.endpoint_zero hEu v]
    have hc0 : chartPt (γ 1) (e ((0 : ℝ) • v)) = chartPt (γ 1) (γ 1) := by
      simp only [zero_smul, H.endpoint_zero]
    have HL : ContDiffAt ℝ 2 (fun r : ℝ => r • v) 0 :=
      (contDiff_id.smul contDiff_const).contDiffAt
    have HC : ContDiffAt ℝ 2 (fun t => chartPt (γ 1) (e t)) ((0 : ℝ) • v) := by
      simpa only [zero_smul] using hchart.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)
    have hcr := HC.comp 0 HL
    have ha := endpointRay_secondJet_of_terminalVariation h (γ 1) e (A 1)
      H.zero_source (P 1).toContinuousLinearMap H.terminal_frame
      (fun z hz => (H.endpoints z hz).2)
      (fun z => by simpa only [one_smul, ContinuousLinearEquiv.coe_coe] using
        (H.jets (γ 1) 1 h1 hc).2.2 z) v
    exact scalar_normalRay_secondDeriv h (γ 1) _ _ hc0 hE hcr v
      (endpointRay_hasDerivAt (γ 1) e hDe v) ha
  rw [hscalar w, hscalar (Complex.I • w)]
  exact covariant_pair_eq_levi h hs hk (γ 1) _ w

def endpointEnergy (h : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (y : M.Carrier) : ℝ :=
  fieldPathEnergy h (fun u => A u (e.symm y))

theorem endpointEnergy_parameter_eq (h : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) :
    Set.EqOn (fun v => fieldPathEnergy h (fun u => A u v))
      (fun v => endpointEnergy h e A (e v)) e.source := by
  intro v hv
  simp only [endpointEnergy, e.left_inv hv]

theorem endpointEnergy_majorant (h : HermitianField M) (hs : MetricSmooth h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier)
    (H : ParallelVariationData h γ δ e P A)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      actualSpeedSq h γ u = inducedDistance h (γ 0) (γ 1)^2) :
    ContDiffAt ℝ 2 (inChart (γ 1) (endpointEnergy h e A)) (chartPt (γ 1) (γ 1)) ∧
    endpointEnergy h e A (γ 1) = inducedDistance h (γ 0) (γ 1)^2 ∧
    ∀ z ∈ e.target, inducedDistance h (γ 0) z ^ 2 ≤ endpointEnergy h e A z := by
  letI := manifold_realSmooth M
  have hStatic : MetricFamilySmooth (fun _ : ℝ => h) Set.univ := by
    intro c i j
    exact (hs c i j).comp contDiffOn_fst (fun _ hp => hp.1)
  obtain ⟨hE, hcontact, hmajorant⟩ := endpointVariation_energy_majorant
    (fun _ : ℝ => h) Set.univ isOpen_univ hStatic (γ 0) (γ 1) 0 (Set.mem_univ _)
    e A γ δ H.delta_pos rfl H.zero_source H.endpoint_zero H.zero H.endpoints hspeed
    H.smooth H.inverse_smooth (hγ.1.of_le (by norm_num))
  refine ⟨?_, hcontact, fun z hz => hmajorant 0 (Set.mem_univ _) z hz⟩
  have HC : ContDiffAt ℝ 2 (fun z : ComplexVector n => (z, (0 : ℝ)))
      (chartPt (γ 1) (γ 1)) := contDiffAt_id.prodMk contDiffAt_const
  have HE := hE.comp (chartPt (γ 1) (γ 1)) HC
  exact HE

theorem endpointEnergy_levi_eq (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier)
    (H : ParallelVariationData h γ δ e P A)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      actualSpeedSq h γ u = inducedDistance h (γ 0) (γ 1)^2) (w : ComplexVector n) :
    4 * complexLeviQuadratic (inChart (γ 1) (endpointEnergy h e A))
      (chartPt (γ 1) (γ 1)) w =
      4 * realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) w w -
        2 * ∫ u in Set.Icc (0 : ℝ) 1, u^2 * parallelBisectional h γ P w u := by
  rw [← parallel_parameter_pair_eq_levi h hs hk γ δ e P A H _ _
    (endpointEnergy_parameter_eq h e A) (endpointEnergy_majorant h hs γ δ e P A H hγ hspeed).1 w]
  exact (parallel_energy_pair h hs hk γ δ e P A H hγ w).2

end Yau.NodeProofs.P02Aux
