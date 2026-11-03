import Yau.LeafProofs.L23FieldMetricVariationLocal

/-! The actual preferred exponential endpoint is a genuine local C3 coordinate equivalence. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem exists_preferred_exp_endpoint
    (h : HermitianField M) (hh : MetricSmooth h) (y : M.Carrier) :
    letI := manifold_realSmooth M
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      (0 : ComplexVector n) ∈ e.source ∧ e 0 = y ∧
      Set.EqOn e (fun v => fieldExp h y (realFrameCLM y y v)) e.source ∧
      ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target := by
  letI := manifold_realSmooth M
  obtain ⟨B,ρ,ε,X,f,H⟩ := exists_fieldNormalEndpointData h hh y Set.univ isOpen_univ (Set.mem_univ _)
  rcases H with ⟨hB,hyB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have Hfull : FieldNormalEndpointData h y Set.univ B ρ ε X f :=
    ⟨hB,hyB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let z := chartPt y y
  let g := fun v : ComplexVector n => X (z,v) 1
  have h1 : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hp (v : ComplexVector n) (hv : v ∈ Metric.ball 0 ρ) : (z,v) ∈ f.source := by rw [hsource]; exact ⟨hyB,hv⟩
  have hg : ContDiffOn ℝ 3 g (Metric.ball 0 ρ) :=
    hX.comp ((contDiffOn_const.prodMk contDiffOn_id).prodMk contDiffOn_const) (fun v hv => ⟨hp v hv,h1⟩)
  have hgAt : ContDiffAt ℝ 3 g 0 := hg.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  have hD : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ (ComplexVector n)).toContinuousLinearMap 0 := (hzero z hyB).2
  have hg0 : g 0 = z := (hzero z hyB).1 1 h1
  let e₀ := hgAt.toOpenPartialHomeomorph g hD (by norm_num)
  have he₀ : (0 : ComplexVector n) ∈ e₀.source := hgAt.mem_toOpenPartialHomeomorph_source hD (by norm_num)
  have Hinv : ContDiffAt ℝ 3 e₀.symm z := by
    rw [← hg0]
    exact hgAt.to_localInverse hD (by norm_num)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (Hinv.eventually (by norm_num))
  let D := Metric.ball (0 : ComplexVector n) ρ ∩ g ⁻¹' Metric.ball z r
  have hDopen : IsOpen D := hg.continuousOn.isOpen_inter_preimage Metric.isOpen_ball Metric.isOpen_ball
  let e₁ := e₀.restrOpen D hDopen
  let e := e₁.trans (chartAt (ComplexVector n) y).symm
  have hsource₀ : (0 : ComplexVector n) ∈ e.source := by
    refine ⟨⟨he₀,Metric.mem_ball_self hρ,?_⟩,?_⟩
    · change g 0 ∈ Metric.ball z r
      rw [hg0]
      exact Metric.mem_ball_self hr
    · change g 0 ∈ (chartAt (ComplexVector n) y).target
      rw [hg0]
      exact (chartAt (ComplexVector n) y).map_source (mem_chart_source _ _)
  have heval (v : ComplexVector n) : e v = chartInv y (g v) := rfl
  have hsrcball (v : ComplexVector n) (hv : v ∈ e.source) : v ∈ Metric.ball 0 ρ := hv.1.2.1
  refine ⟨e,hsource₀,?_,?_,?_⟩
  · rw [heval,hg0]
    exact (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  · intro v hv
    rw [heval]
    have HN := fieldExp_normal_coordinates h hh y y Set.univ B ρ ε X f Hfull (mem_chart_source _ _)
      (realFrameCLM y y v) (by rw [realTangentCoords_realFrameCLM y y (mem_chart_source _ _)]; exact hp v (hsrcball v hv))
    simpa only [realTangentCoords_realFrameCLM y y (mem_chart_source _ _),g,z] using HN.symm
  · intro x hx
    have hv := e.map_target hx
    have hmetric : g (e.symm x) ∈ Metric.ball z r := hv.1.2.2
    have hchart : x ∈ (chartAt (ComplexVector n) y).source := hx.1
    have hcoord : g (e.symm x) = chartPt y x := by
      have Hright := (e₀.right_inv (e₀.map_source hv.1.1))
      change g (e₀.symm (g (e.symm x))) = g (e.symm x) at Hright
      have Hpoint : e (e.symm x) = x := e.right_inv hx
      have Hc := congrArg (chartPt y) Hpoint
      rw [heval] at Hc
      have Htarget : g (e.symm x) ∈ (extChartAt (ComplexModel n) y).target := by
        rw [extChartAt_target]
        constructor
        · change g (e.symm x) ∈ (chartAt (ComplexVector n) y).target
          exact hv.2
        · exact ⟨g (e.symm x),rfl⟩
      exact ((extChartAt (ComplexModel n) y).right_inv Htarget).symm.trans Hc
    have HI : ContDiffAt ℝ 3 e₀.symm (chartPt y x) := hrsub (hcoord ▸ hmetric)
    have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (chartPt y) x := by
      convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3) (x := y) (x' := x) hchart) using 1
    exact (HI.contMDiffAt.comp x HC).contMDiffWithinAt

end Yau.LeafProofs.L23Aux
