import Yau.LeafProofs.L23DistanceEnergyRayCharts

/-! The original manifold energy density has the computed true second variation. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

variable {n : ℕ} {M : ComplexManifold n}

theorem rayEnergyDensity_secondDeriv
    (h : HermitianField M) (hh : MetricSmooth h)
    (A : ℝ → ComplexVector n → M.Carrier) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (U : Set (ComplexVector n)) (hJ : IsOpen J) (hU : IsOpen U)
    (hzero : (0 : ComplexVector n)∈U) (hA0 : ∀ s∈J, A s 0=γ s)
    (w : ComplexVector n) (u : ℝ) (hu : u∈J) (c : M.Carrier)
    (hc : γ u∈(chartAt (ComplexVector n) c).source) (P : ℝ → ComplexVector n)
    (hFirst : ∀ᶠ s in 𝓝 u,
      HasDerivAt (fun r : ℝ => chartPt c (A s (r • w))) (s • P s) 0)
    (hSecond : ∀ᶠ s in 𝓝 u,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (A s (r • w))))
        (-chartChristoffelBilin h c (chartPt c (γ s)) (s • P s) (s • P s)) 0)
    (hParallel : HasDerivAt P
      (-chartChristoffelBilin h c (chartPt c (γ u)) (deriv (fun s => chartPt c (γ s)) u) (P u)) u) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u^2)) 0=
      2*realMetricInChart h c (chartPt c (γ u)) (P u) (P u)+
      2*realMetricInChart h c (chartPt c (γ u)) (deriv (fun s => chartPt c (γ s)) u)
        (connectionCurvature (chartChristoffelBilin h c) (chartPt c (γ u))
          (u • P u) (deriv (fun s => chartPt c (γ s)) u) (u • P u)) := by
  letI := manifold_realSmooth M
  intro hA
  let Z : ℝ × ℝ → ComplexVector n := fun p => chartPt c (A p.2 (p.1 • w))
  have hc0 : A u 0∈(chartAt (ComplexVector n) c).source := by rw [hA0 u hu]; exact hc
  have hzero' : (0 : ℝ) • w∈U := by simpa only [zero_smul] using hzero
  have hZ : ContDiffAt ℝ 3 Z (0,u) :=
    rayVariation_chart_contDiffAt A J U hJ hU w 0 u hu hzero' c (by simpa only [zero_smul] using hc0) hA
  have hZ₂ : ContDiffAt ℝ 2 Z (0,u) := hZ.of_le (by norm_num)
  have hZ0 : Z (0,u)=chartPt c (γ u) := by simp only [Z,zero_smul,hA0 u hu]
  have hz : Z (0,u)∈chartTarget c := by
    rw [hZ0]
    exact (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hc)
  have hnearZ : ∀ᶠ s in 𝓝 u, ContDiffAt ℝ 2 Z (0,s) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      (hZ₂.eventually (by norm_num))
  have hJEq : (fun s => mapDirection Z (1,0) (0,s))=ᶠ[𝓝 u] (fun s => s • P s) := by
    filter_upwards [hFirst,hnearZ] with s hs hsZ
    exact (mapDirection_fst_eq_deriv Z (hsZ.differentiableAt (by norm_num))).trans hs.deriv
  have hJval : mapDirection Z (1,0) (0,u)=u • P u := hJEq.self_of_nhds
  have hγEq : (fun s => Z (0,s))=ᶠ[𝓝 u] (fun s => chartPt c (γ s)) := by
    filter_upwards [hJ.mem_nhds hu] with s hs
    simp only [Z,zero_smul,hA0 s hs]
  have hT : mapDirection Z (0,1) (0,u)=deriv (fun s => chartPt c (γ s)) u := by
    rw [mapDirection_snd_eq_deriv Z (hZ.differentiableAt (by norm_num)),hγEq.deriv_eq]
  have hP' : HasDerivAt P
      (-chartChristoffelBilin h c (Z (0,u)) (mapDirection Z (0,1) (0,u)) (P u)) u := by
    rw [hZ0,hT]
    exact hParallel
  have hL := mapCovariantD_linear_parallelVariation (chartChristoffelBilin h c) Z hZ₂ P hP' hJEq
  have hLr : mapCovariantD (chartChristoffelBilin h c) Z (1,0) (mapDirection Z (0,1)) (0,u)=P u :=
    (mapCovariantD_torsionFree _ Z hZ₂ (chartChristoffelBilin_symm h c (Z (0,u))) (1,0) (0,1)).trans hL
  have hRadial : ∀ᶠ s in 𝓝 u,
      deriv (deriv (fun r => Z (r,s))) 0=
        -chartChristoffelBilin h c (Z (0,s)) (mapDirection Z (1,0) (0,s))
          (mapDirection Z (1,0) (0,s)) := by
    filter_upwards [hSecond,hJEq,hJ.mem_nhds hu] with s hs hsJ hsI
    rw [hsJ]
    simpa only [Z,zero_smul,hA0 s hsI] using hs.deriv
  have hRad := mapCovariantD_radialAcceleration_zero h hh c Z hz hZ hRadial
  have hVar := mapEnergyDensity_secondVariation h hh c Z hz hZ (1,0) (0,1) hRad
  have heq := rayEnergyDensity_chart_eventuallyEq h A J U hJ hU w u hu hzero c hc0 hA
  have heqR : (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u^2)=ᶠ[𝓝 (0 : ℝ)]
      (fun r => realMetricInChart h c (Z (r,u))
        (mapDirection Z (0,1) (r,u)) (mapDirection Z (0,1) (r,u))) :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds heq
  have hG : ContDiffAt ℝ 2 (fun p => realMetricInChart h c (Z p)) (0,u) :=
    (((realMetricInChart_smooth h hh c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).of_le (by simp)).comp (0,u) hZ₂
  have hVel : ContDiffAt ℝ 2 (mapDirection Z (0,1)) (0,u) := mapDirection_contDiffAt Z 2 hZ (0,1)
  have hDensity := (hG.clm_apply hVel).clm_apply hVel
  rw [heqR.deriv.deriv_eq,←mapDirection_fst_second_eq_deriv _ hDensity]
  simpa only [hLr,hJval,hT,hZ0] using hVar

end Yau.LeafProofs.L23Aux
