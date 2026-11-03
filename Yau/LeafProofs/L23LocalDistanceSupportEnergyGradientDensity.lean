import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradientPairing

/-! Actual first variation of the original physical speed square. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

theorem fieldPathSpeedSq_parallelVariation_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (s : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ s))
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) (U : Set (ComplexVector n))
    (hJ : IsOpen J) (hU : IsOpen U) (h0 : (0 : ComplexVector n) ∈ U)
    (hγ : FieldGeodesicOn h γ J) (hA0 : ∀ s ∈ J, A s 0 = γ s)
    (hP : ∀ (c : M.Carrier) (s : ℝ), s ∈ J → γ s ∈ (chartAt (ComplexVector n) c).source →
      ∀ w : ComplexVector n, HasDerivAt (fun r => realTangentCoords c (γ r) (P r w))
        (-chartChristoffelBilin h c (chartPt c (γ s)) (geoChartState γ c s).2
          (realTangentCoords c (γ s) (P s w))) s)
    (hfirst : ∀ (c : M.Carrier) (s : ℝ), s ∈ J → γ s ∈ (chartAt (ComplexVector n) c).source →
      HasFDerivAt (fun v => chartPt c (A s v))
        (s • ((realTangentCoords c (γ s)).comp (P s).toContinuousLinearMap)) 0) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ U) →
    ∀ u ∈ J, ∀ w : ComplexVector n,
      HasDerivAt (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u ^ 2)
        (2*(underlyingRealRiemannianMetric h).inner (γ u) (realCurveVelocity γ u) (P u w)) 0 := by
  letI := manifold_realSmooth M
  intro hA u hu w
  let c := γ u
  let Z := fun p : ℝ × ℝ => chartPt c (A p.2 (p.1 • w))
  let W := fun s => realTangentCoords c (γ s) (P s w)
  have hγc : γ u ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hAat : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (u,0) := (hA (u,0) ⟨hu,h0⟩).contMDiffAt ((hJ.prod hU).mem_nhds ⟨hu,h0⟩)
  have HM : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3
      (fun p : ℝ × ℝ => (p.2,p.1 • w)) (0,u) := by
    exact contDiffAt_snd.contMDiffAt.prodMk (contDiffAt_fst.smul_const w).contMDiffAt
  have HAline : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ℝ × ℝ => A p.2 (p.1 • w)) (0,u) := by
    have HApoint : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
        (Function.uncurry A) ((fun p : ℝ × ℝ => (p.2,p.1 • w)) (0,u)) := by
      simpa only [zero_smul] using hAat
    exact HApoint.comp (0,u) HM
  have hAzero : A u ((0 : ℝ) • w) = γ u := by rw [zero_smul,hA0 u hu]
  have hAC : A u ((0 : ℝ) • w) ∈ (chartAt (ComplexVector n) c).source := by rw [hAzero]; exact hγc
  have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (chartPt c) (A u ((0 : ℝ) • w)) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3)
      (x := c) (x' := A u ((0 : ℝ) • w)) hAC) using 1
  have HZ : ContDiffAt ℝ 2 Z (0,u) := ((HC.comp (0,u) HAline).contDiffAt).of_le (by norm_num)
  have Hbase : (fun s => Z (0,s)) =ᶠ[𝓝 u] (fun s => chartPt c (γ s)) := by
    filter_upwards [hJ.mem_nhds hu] with s hs
    simp only [Z,zero_smul,hA0 s hs]
  have Hbase0 : Z (0,u) = chartPt c (γ u) := Hbase.self_of_nhds
  have hcont : ContinuousAt γ u := hγ.1.continuousOn.continuousAt (hJ.mem_nhds hu)
  have Hs : ∀ᶠ s in 𝓝 u, s ∈ J ∧ γ s ∈ (chartAt (ComplexVector n) c).source :=
    inter_mem (hJ.mem_nhds hu) (hcont.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds hγc))
  have Hvar : ∀ᶠ s in 𝓝 u, deriv (fun r => Z (r,s)) 0 = s • W s := by
    filter_upwards [Hs] with s hs
    have HD : HasDerivAt (fun r : ℝ => r • w) w 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have HF : HasFDerivAt (fun v => chartPt c (A s v))
        (s • ((realTangentCoords c (γ s)).comp (P s).toContinuousLinearMap)) ((0 : ℝ) • w) := by
      simpa only [zero_smul] using hfirst c s hs.1 hs.2
    convert! (HF.comp_hasDerivAt 0 HD).deriv using 1 <;>
      simp only [Z,W,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  have HW : HasDerivAt W (-chartChristoffelBilin h c (Z (0,u)) (deriv (fun s => Z (0,s)) u) (W u)) u := by
    rw [Hbase0,Hbase.deriv_eq]
    exact hP c u hu hγc w
  have hz : Z (0,u) ∈ chartTarget c := by rw [Hbase0]; exact mem_extChartAt_target c
  have H := chartEnergy_parallelVariation_hasDerivAt h hh c Z W u HZ hz Hvar HW
  have Hγu : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
    ((hγ.1 u hu).contMDiffAt (hJ.mem_nhds hu)).of_le (by norm_num)
  have HCγ : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (γ u) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1) (x := c) (x' := γ u) hγc) using 1
  have HDγ : HasDerivAt (fun s => chartPt c (γ s)) (deriv (fun s => chartPt c (γ s)) u) u :=
    ((HCγ.comp u Hγu).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have HV := realCurveVelocity_coords_of_hasDerivAt γ u c _ hγc (Hγu.mdifferentiableAt (by norm_num)) HDγ
  have HMmetric := realMetricInChart_tangentCoords h c (γ u) hγc (realCurveVelocity γ u) (P u w)
  rw [HV] at HMmetric
  rw [Hbase0,Hbase.deriv_eq] at H
  dsimp only [W] at H
  rw [HMmetric] at H
  apply H.congr_of_eventuallyEq
  have Hline : ContinuousAt (fun r : ℝ => ((0 : ℝ)+r,u)) 0 := by fun_prop
  have Hsource : ∀ᶠ r in 𝓝 (0 : ℝ), A u (r • w) ∈ (chartAt (ComplexVector n) c).source := by
    have HR : ContinuousAt (fun r : ℝ => (r,u)) 0 := continuousAt_id.prodMk continuousAt_const
    have HD : ContinuousAt (fun r : ℝ => A u (r • w)) 0 :=
      HAline.continuousAt.comp (f := fun r : ℝ => (r,u)) HR
    exact HD.preimage_mem_nhds ((chartAt (ComplexVector n) c).open_source.mem_nhds hAC)
  have HU : ∀ᶠ r in 𝓝 (0 : ℝ), r • w ∈ U := by
    have HR : ContinuousAt (fun r : ℝ => r • w) 0 := (continuous_id.smul continuous_const).continuousAt
    apply HR.preimage_mem_nhds
    change U ∈ 𝓝 ((0 : ℝ) • w)
    rw [zero_smul]
    exact hU.mem_nhds h0
  filter_upwards [Hsource,HU] with r hr hru
  have HFiber : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (fun s => A s (r • w)) u := by
    have HAt := (hA (u,r • w) ⟨hu,hru⟩).contMDiffAt ((hJ.prod hU).mem_nhds ⟨hu,hru⟩)
    have HMap : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3 (fun s : ℝ => (s,r • w)) u :=
      contMDiffAt_id.prodMk contMDiffAt_const
    have HF3 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 (fun s => A s (r • w)) u := HAt.comp u HMap
    exact HF3.of_le (by norm_num)
  have HChart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (A u (r • w)) := by
    convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1) (x := c) (x' := A u (r • w)) hr) using 1
  have HD := ((HChart.comp u HFiber).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  exact fieldPathSpeed_sq_eq_chartDerivative h _ c u hr _ (HFiber.mdifferentiableAt (by norm_num)) HD

end Yau.LeafProofs.L23Aux
