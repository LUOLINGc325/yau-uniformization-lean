import Yau.LeafProofs.L23FieldMetricUnitGeodesic
import Yau.LeafProofs.L23FieldMetricGeodesic

/-! A joint C3 family of genuine unit-parameter local geodesics, contained
in any prescribed open neighborhood of its base point. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem exists_C3_unit_chart_geodesic_family
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (O : Set M.Carrier) (hO : IsOpen O) (hc : c ∈ O) :
    ∃ (B : Set (ComplexVector n)) (ρ δ : ℝ)
      (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n),
      IsOpen B ∧ chartPt c c ∈ B ∧ B ⊆ chartTarget c ∧ 0 < ρ ∧ 0 < δ ∧
      ContDiffOn ℝ 3 (Function.uncurry η)
        ((B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-δ) (1+δ)) ∧
      (∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
        η p 0 = p ∧
        (∀ u ∈ Set.Ioo (-δ) (1+δ), (η p u).1 ∈ chartTarget c ∧
          HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u) ∧
        FieldGeodesicOn h (fun u => chartInv c (η p u).1) (Set.Ioo (-δ) (1+δ)) ∧
        Set.MapsTo (fun u => chartInv c (η p u).1) (Set.Icc (0 : ℝ) 1) O) ∧
      ∀ z ∈ B,
        (∀ u ∈ Set.Ioo (-δ) (1+δ), η (z,0) u = (z,0)) ∧
        HasFDerivAt (fun v => (η (z,v) 1).1)
          (ContinuousLinearMap.id ℝ (ComplexVector n)) 0 := by
  let Upos := chartTarget c ∩ (chartInv c) ⁻¹' O
  have hInvCont : ContinuousOn (chartInv c) (chartTarget c) :=
    continuousOn_extChartAt_symm (I := ComplexModel n) c
  have hUpos : IsOpen Upos := hInvCont.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel n) c) hO
  have hzc : chartPt c c ∈ Upos := by
    refine ⟨mem_extChartAt_target c,?_⟩
    change chartInv c (chartPt c c) ∈ O
    have hinv : chartInv c (chartPt c c) = c :=
      (extChartAt (ComplexModel n) c).left_inv (mem_extChartAt_source c)
    rw [hinv]
    exact hc
  let Ubase := Upos ×ˢ (Set.univ : Set (ComplexVector n))
  have hUbase : IsOpen Ubase := hUpos.prod isOpen_univ
  have hSprayBase : ContDiffOn ℝ ∞ (chartGeodesicSpray h c) Ubase :=
    (chartGeodesicSpray_contDiffOn h hh c).mono (fun p hp => ⟨hp.1.1,hp.2⟩)
  have hpbase : (chartPt c c,(0 : ComplexVector n)) ∈ Ubase := ⟨hzc,Set.mem_univ _⟩
  obtain ⟨K,W,hW,hLipW⟩ := ((hSprayBase.contDiffAt (hUbase.mem_nhds hpbase)).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  obtain ⟨R₀,hR₀,hR₀sub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hUbase.mem_nhds hpbase))
  let U := Metric.ball (chartPt c c,(0 : ComplexVector n)) R₀
  have hU : IsOpen U := Metric.isOpen_ball
  have hUsub : U ⊆ Ubase := fun p hp => (hR₀sub hp).2
  have hLipU : LipschitzOnWith K (chartGeodesicSpray h c) U :=
    hLipW.mono (fun p hp => (hR₀sub hp).1)
  have hSpray : ContDiffOn ℝ ∞ (chartGeodesicSpray h c) U := hSprayBase.mono hUsub
  obtain ⟨r,hr,ε,hε,φ,V,hφ,hV,hi,hs,hx,hJ⟩ := localODEFlowOrder 3
    (ComplexVector n × ComplexVector n) (chartGeodesicSpray h c) U
      (chartPt c c,0) hSpray hU (Metric.mem_ball_self hR₀)
  let e := ε/4
  have he : 0 < e := div_pos hε (by norm_num)
  let B := Metric.ball (chartPt c c) (r/2) ∩ Upos
  let ρ := e*r/2
  let δ : ℝ := 1/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hδ : 0 < δ := by norm_num [δ]
  let D := (B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-δ) (1+δ)
  have hmap : ∀ p ∈ D, ((p.1.1,e⁻¹ • p.1.2),e*p.2) ∈
      Metric.ball (chartPt c c,0) r ×ˢ Set.Ioo (-ε) ε := by
    intro p hp
    constructor
    · rw [Metric.mem_ball,Prod.dist_eq,dist_zero_right]
      apply max_lt_iff.mpr
      constructor
      · exact (Metric.mem_ball.mp hp.1.1.1).trans (half_lt_self hr)
      · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos he]
        have hv : ‖p.1.2‖ < ρ := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1.2
        have H : ‖p.1.2‖/e < r := (div_lt_iff₀ he).mpr (by dsimp [ρ] at hv; nlinarith)
        simpa only [div_eq_mul_inv,mul_comm] using H
    · have Hlo := mul_lt_mul_of_pos_left hp.2.1 he
      have Hhi := mul_lt_mul_of_pos_left hp.2.2 he
      dsimp [δ,e] at Hlo Hhi
      change -ε < (ε/4)*p.2 ∧ (ε/4)*p.2 < ε
      constructor <;> nlinarith
  let η := normalizedChartFlow e φ
  have hηC3 : ContDiffOn ℝ 3 (Function.uncurry η) D :=
    normalizedChartFlow_contDiffOn e φ hφ hmap
  have hηsol : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
      ∀ u ∈ Set.Ioo (-δ) (1+δ),
        (η p u).1 ∈ chartTarget c ∧
          HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u := by
    intro p hp u hu
    have H := hs _ (hmap (p,u) ⟨hp,hu⟩).1 _ (hmap (p,u) ⟨hp,hu⟩).2
    exact ⟨(hUsub H.1).1.1,normalizedChartFlow_hasDerivAt h c e φ p u H.2.1⟩
  refine ⟨B,ρ,δ,η,Metric.isOpen_ball.inter hUpos,
    ⟨Metric.mem_ball_self (half_pos hr),hzc⟩,
    (fun z hz => hz.2.1),hρ,hδ,hηC3,?_,?_⟩
  · intro p hp
    have hzero : (0 : ℝ) ∈ Set.Ioo (-δ) (1+δ) := by constructor <;> linarith
    have hinit : η p 0 = p := normalizedChartFlow_initial e he.ne' φ p
      (hi _ (hmap (p,0) ⟨hp,hzero⟩).1).1
    have hηslice : ContDiffOn ℝ 3 (η p) (Set.Ioo (-δ) (1+δ)) :=
      hηC3.comp (contDiffOn_const.prodMk contDiffOn_id) (fun u hu => ⟨hp,hu⟩)
    refine ⟨hinit,hηsol p hp,
      fieldGeodesicOn_of_chart_solution h hh c (η p) isOpen_Ioo hηslice (hηsol p hp),?_⟩
    intro u hu
    have hu' : u ∈ Set.Ioo (-δ) (1+δ) := by constructor <;> linarith [hu.1,hu.2]
    exact (hUsub (hs _ (hmap (p,u) ⟨hp,hu'⟩).1 _ (hmap (p,u) ⟨hp,hu'⟩).2).1).1.2
  · intro z hz
    have h₀ : (0 : ℝ) ∈ Set.Ioo (-δ) (1+δ) := by constructor <;> linarith
    have hp : ((z,0) : ComplexVector n × ComplexVector n) ∈
        B ×ˢ Metric.ball (0 : ComplexVector n) ρ := ⟨hz,Metric.mem_ball_self hρ⟩
    have hzball : ((z,0) : ComplexVector n × ComplexVector n) ∈ Metric.ball (chartPt c c,0) r := by
      simpa only [smul_zero] using (hmap ((z,0),0) ⟨hp,h₀⟩).1
    have h₀ε : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
    have hzU : ((z,0) : ComplexVector n × ComplexVector n) ∈ U := by
      have H := (hs _ hzball 0 h₀ε).1
      rw [(hi _ hzball).1] at H
      exact H
    have hstation := zeroSpeed_flow_stationary h c z U K hLipU φ hε hzU
      (hi _ hzball).1 (fun t ht => ⟨(hs _ hzball t ht).1,(hs _ hzball t ht).2.1⟩)
    refine ⟨?_,?_⟩
    · intro u hu
      have H := hstation (e*u) (hmap ((z,0),u) ⟨hp,hu⟩).2
      dsimp only [η,normalizedChartFlow]
      simp only [smul_zero,H]
    · have heε : e ∈ Set.Ioo (-ε) ε := by dsimp [e]; constructor <;> linarith
      have Hend := zeroSpeed_flow_endpoint_derivative h hh c z hz.2.1 φ V hε heε
        (hi _ hzball).2 hstation (fun t ht => (hs _ hzball t ht).2.2)
          (hx ((z,0),e) ⟨hzball,heε⟩)
      have Hend' : HasFDerivAt (fun v => (φ (z,v) e).1)
          (e • ContinuousLinearMap.id ℝ (ComplexVector n)) (e⁻¹ • (0 : ComplexVector n)) := by
        simpa only [smul_zero] using Hend
      have H := Hend'.comp 0 ((hasFDerivAt_id (0 : ComplexVector n)).const_smul e⁻¹)
      convert! H using 1
      · funext v
        simp only [η,normalizedChartFlow,mul_one,Function.comp_apply]
      · apply ContinuousLinearMap.ext
        intro w
        simp [ContinuousLinearMap.comp_apply,smul_smul,he.ne']

end Yau.LeafProofs.L23Aux
