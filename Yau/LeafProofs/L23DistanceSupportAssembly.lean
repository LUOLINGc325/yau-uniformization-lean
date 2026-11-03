import Yau.LeafProofs.L23DistanceEnergyLaplacian
import Yau.LeafProofs.L23LocalDistanceSupportEnergyLaplacianTrace
import Yau.LeafProofs.L23LocalDistanceSupportEnergyTime
import Yau.LeafProofs.L23LocalDistanceSupportEnergyMajorant
import Yau.LeafProofs.L23LocalDistanceSupportMinimizingGeodesicFlow

/-! A genuine fixed-path energy gives all local distance-square support jets. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_timeDistanceSq_upperSupport
    (h : ℝ → HermitianField M) (p q y : M.Carrier)
    (a K r τ σ rIn rOut t : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x∈distBall (h a) p (2*r), ∀ s∈Set.Icc a (a+2*τ), curvatureJetNorm (h s) 0 x≤K)
    (hIn : 0<rIn) (hInOut : rIn<rOut) (hOut : rOut≤2*r)
    (hq : q∈distBall (h a) p rIn) (ht : t∈Set.Ioo a (a+2*τ))
    (hy : inducedDistance (h t) q y<Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) :
    ∃ E : M.Carrier → ℝ → ℝ,
      ContDiffAt ℝ 2 (fun z : ComplexVector n × ℝ => E (chartInv y z.1) z.2) (chartPt y y,t) ∧
      E y t=inducedDistance (h t) q y^2 ∧
      (∀ᶠ z in 𝓝 (y,t), inducedDistance (h z.2) q z.1^2≤E z.1 z.2) ∧
      realGradPair (h t) (fun z => E z t) (fun z => E z t) y=4*inducedDistance (h t) q y^2 ∧
      realLap (h t) (fun z => E z t) y≤
        2*(2*n : ℕ)+(2/3 : ℝ)*(2*n : ℕ)*K*inducedDistance (h t) q y^2 ∧
      -σ*(2*n : ℕ)*K*inducedDistance (h t) q y^2≤deriv (E y) t := by
  letI := manifold_realSmooth M
  have htC : t∈Set.Icc a (a+2*τ) := ⟨ht.1.le,ht.2.le⟩
  have hh := metricFamilySmooth_slice h hflow.1 htC
  obtain ⟨ε,hε,γ,hγ0,hγ1,hGeo,hγO,hspeed⟩ := exists_buffered_minimizing_geodesic
    h p q y a K r τ σ rIn rOut t hK hr hτ hσ hO hcO hflow hcurv hIn hInOut hOut hq htC hy
  obtain ⟨δ,e,P,A,hδ,hδε,hzero,he0,hA,hinv,hA0,hend,hP1,hPair,hJets⟩ :=
    parallelEndpointVariation n M (h t) hh (distBall (h a) p (2*r)) hO γ ε hε hGeo hγO
  have hsub : Set.Ioo (-δ) (1+δ) ⊆ Set.Ioo (-ε) (1+ε) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hGeoδ : FieldGeodesicOn (h t) γ (Set.Ioo (-δ) (1+δ)) :=
    ⟨hGeo.1.mono hsub,fun c u hu hc => hGeo.2 c u (hsub hu) hc⟩
  have hP (c : M.Carrier) (u : ℝ) (hu : u∈Set.Ioo (-δ) (1+δ))
      (hc : γ u∈(chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).1
  have hFirst (c : M.Carrier) (u : ℝ) (hu : u∈Set.Ioo (-δ) (1+δ))
      (hc : γ u∈(chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).2.1
  have hSecond (c : M.Carrier) (u : ℝ) (hu : u∈Set.Ioo (-δ) (1+δ))
      (hc : γ u∈(chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).2.2
  have hcurvγ (u : ℝ) (hu : u∈Set.Icc (0 : ℝ) 1) : curvatureJetNorm (h t) 0 (γ u)≤K :=
    hcurv (γ u) (hγO hu) t htC
  have Hfam : MetricFamilySmooth h (Set.Ioo a (a+2*τ)) := by
    intro c i j
    exact (hflow.1 c i j).mono (fun z hz => ⟨hz.1,⟨hz.2.1.le,hz.2.2.le⟩⟩)
  obtain ⟨hE,hval,hupper⟩ := endpointVariation_energy_majorant h (Set.Ioo a (a+2*τ)) isOpen_Ioo Hfam
    q y t ht e A γ δ hδ hγ1 hzero (he0.trans hγ1) hA0
    (fun v hv => ⟨(hend v hv).1.trans hγ0,(hend v hv).2.1⟩) hspeed hA hinv
      (hGeoδ.1.of_le (by norm_num))
  have hgrad := realGradPair_endpointVariation_fieldPathEnergy (h t) hh γ P e A δ hδ hGeoδ hzero he0 hA0
    (fun v hv => (hend v hv).2.1) hP1 hP hFirst hA hinv
  rw [hspeed 1 (by norm_num),hγ1] at hgrad
  let b := fieldOrthonormalFrame (h t) (γ 1)
  have h1 : (1 : ℝ)∈Set.Ioo (-δ) (1+δ) := by constructor <;> linarith
  have hF1 : HasFDerivAt (fun v => chartPt (γ 1) (A 1 v))
      ((realTangentCoords (γ 1) (γ 1)).comp (P 1).toContinuousLinearMap) 0 := by
    simpa only [one_smul] using hFirst (γ 1) 1 h1 (mem_chart_source _ _)
  have hS1 (w : ComplexVector n) : HasDerivAt (deriv (fun s : ℝ => chartPt (γ 1) (A 1 (s • w))))
      (-chartChristoffelBilin (h t) (γ 1) (chartPt (γ 1) (γ 1))
        (realTangentCoords (γ 1) (γ 1) ((P 1).toContinuousLinearMap w))
        (realTangentCoords (γ 1) (γ 1) ((P 1).toContinuousLinearMap w))) 0 := by
    simpa only [one_smul,ContinuousLinearEquiv.coe_coe] using hSecond (γ 1) 1 h1 (mem_chart_source _ _) w
  have hTrace := realLap_endpointVariation_fieldPathEnergy_eq_secondDeriv_sum (h t) hh (γ 1) e A δ hδ
    hzero he0 (P 1).toContinuousLinearMap hP1 (fun v hv => (hend v hv).2.1) hF1 hS1 b hA hinv
  have hlap := realLap_endpointVariation_fieldPathEnergy_le_of_trace (h t) hh γ P e A δ K
    (inducedDistance (h t) q y) hδ hzero hGeoδ hA0 hPair hP hFirst hSecond hcurvγ hspeed b hTrace hA
  rw [hγ1] at hlap
  have hdt := endpointVariation_fieldPathEnergy_time_deriv_lower h (distBall (h a) p (2*r))
    a (a+2*τ) σ K (inducedDistance (h t) q y) hσ.le hflow hcurv γ e A δ hδ hzero he0 hA0 hγO
    t ht hspeed hA hGeoδ.1
  rw [hγ1] at hdt
  refine ⟨fun z s => fieldPathEnergy (h s) (fun u => A u (e.symm z)),hE,hval,?_,hgrad,hlap,hdt⟩
  have hyT : y∈e.target := by rw [←(he0.trans hγ1)]; exact e.map_source hzero
  filter_upwards [(e.open_target.prod isOpen_Ioo).mem_nhds
    (show (y,t)∈e.target ×ˢ Set.Ioo a (a+2*τ) from ⟨hyT,ht⟩)] with z hz
  exact hupper z.2 hz.2 z.1 hz.1

end Yau.LeafProofs.L23Aux
