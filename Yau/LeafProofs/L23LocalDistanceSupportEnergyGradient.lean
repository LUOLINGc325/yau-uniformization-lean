import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradientIntegral
import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradientAlgebra

/-! The exact physical gradient norm of the genuine parallel-endpoint path energy. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1500000

theorem realGradPair_endpointVariation_fieldPathEnergy
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = γ 1)
    (hA0 : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u)
    (hend : ∀ v ∈ e.source, A 1 v = e v)
    (hP1 : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1))
    (hP : ∀ (c : M.Carrier) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) → γ u ∈ (chartAt (ComplexVector n) c).source →
      ∀ w : ComplexVector n, HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin h c (chartPt c (γ u)) (geoChartState γ c u).2
          (realTangentCoords c (γ u) (P u w))) u)
    (hfirst : ∀ (c : M.Carrier) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) → γ u ∈ (chartAt (ComplexVector n) c).source →
      HasFDerivAt (fun v => chartPt c (A u v))
        (u • ((realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)) 0) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target →
    realGradPair h (fun z => fieldPathEnergy h (fun u => A u (e.symm z)))
      (fun z => fieldPathEnergy h (fun u => A u (e.symm z))) (γ 1) =
        4*actualSpeedSq h γ 1 := by
  letI := manifold_realSmooth M
  intro hA hinv
  let J := Set.Ioo (-δ) (1+δ)
  let E := fun z : M.Carrier => fieldPathEnergy h (fun u => A u (e.symm z))
  let Eu := fun v : ComplexVector n => fieldPathEnergy h (fun u => A u v)
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ J := by intro u hu; constructor <;> linarith [hu.1,hu.2]
  have h1 : (1 : ℝ) ∈ J := hunit (by norm_num)
  have Hfam : MetricFamilySmooth (fun _ : ℝ => h) Set.univ := by
    intro c i j
    exact (hh c i j).comp contDiffOn_fst (fun p hp => hp.1)
  have HS := endpointVariation_fieldPathEnergy_contDiffOn_two (fun _ : ℝ => h) Set.univ isOpen_univ Hfam
    (γ 1) e A J isOpen_Ioo hunit hA hinv
  have hU : IsOpen (chartTarget (γ 1) ∩ (chartInv (γ 1)) ⁻¹' e.target) :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) (γ 1)).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel n) (γ 1)) e.open_target
  have hy : γ 1 ∈ e.target := by rw [← he0]; exact e.map_source h0
  have hinvy : chartInv (γ 1) (chartPt (γ 1) (γ 1)) = γ 1 :=
    (extChartAt (ComplexModel n) (γ 1)).left_inv (mem_extChartAt_source _)
  have hpoint : (chartPt (γ 1) (γ 1),(0 : ℝ)) ∈
      (chartTarget (γ 1) ∩ (chartInv (γ 1)) ⁻¹' e.target) ×ˢ (Set.univ : Set ℝ) := by
    refine ⟨⟨mem_extChartAt_target _,?_⟩,Set.mem_univ _⟩
    change chartInv (γ 1) (chartPt (γ 1) (γ 1)) ∈ e.target
    rwa [hinvy]
  have HSAt := HS.contDiffAt ((hU.prod isOpen_univ).mem_nhds hpoint)
  have HE : DifferentiableAt ℝ (inChart (γ 1) E) (chartPt (γ 1) (γ 1)) :=
    (HSAt.comp (chartPt (γ 1) (γ 1)) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have HF1 : HasFDerivAt (fun v => chartPt (γ 1) (A 1 v))
      ((realTangentCoords (γ 1) (γ 1)).comp (P 1).toContinuousLinearMap) 0 := by
    simpa only [one_smul] using hfirst (γ 1) 1 h1 (mem_chart_source _ _)
  have HDe := endpointChart_hasFDerivAt_id (γ 1) e (fun v => A 1 v) h0 (P 1).toContinuousLinearMap hP1
    (fun v hv => hend v hv) HF1
  have HEu : Set.EqOn Eu (fun v => E (e v)) e.source := by
    intro v hv
    change fieldPathEnergy h (fun u => A u v) = fieldPathEnergy h (fun u => A u (e.symm (e v)))
    rw [e.left_inv hv]
  have Hdir (w : ComplexVector n) : HasDerivAt (fun r : ℝ => Eu (r • w))
      (2*realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1))
        (realTangentCoords (γ 1) (γ 1) (realCurveVelocity γ 1)) w) 0 := by
    let C := 2*(underlyingRealRiemannianMetric h).inner (γ 1) (realCurveVelocity γ 1) (P 1 w)
    have Hdensity (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivAt (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u ^ 2) C 0 := by
      have H := fieldPathSpeedSq_parallelVariation_hasDerivAt h hh γ P A J e.source isOpen_Ioo e.open_source h0
        hγ hA0 hP hfirst hA u (hunit hu) w
      have HC := geodesic_parallel_pairing_constant h hh γ (fun s => P s w) (-δ) (1+δ) hγ
        (fun c s hs hc => hP c s hs hc w) u 1 (hunit hu) h1
      rwa [HC] at H
    have H := fieldPathEnergy_hasDerivAt_of_constant_density_firstVariation h hh A e.source J e.open_source isOpen_Ioo
      h0 hunit w C Hdensity hA
    change HasDerivAt (fun r : ℝ => Eu (r • w))
      (2*(underlyingRealRiemannianMetric h).inner (γ 1) (realCurveVelocity γ 1) ((P 1).toContinuousLinearMap w)) 0 at H
    rw [hP1] at H
    have HM := realMetricInChart_tangentCoords h (γ 1) (γ 1) (mem_chart_source _ _)
      (realCurveVelocity γ 1) (realFrameCLM (γ 1) (γ 1) w)
    rw [realTangentCoords_realFrameCLM _ _ (mem_chart_source _ _)] at HM
    rwa [← HM] at H
  exact realGradPair_of_endpoint_parameter_directions h (γ 1) E Eu e h0 he0 HDe HEu HE
    (realCurveVelocity γ 1) Hdir

end Yau.LeafProofs.L23Aux
