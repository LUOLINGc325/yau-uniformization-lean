import Yau.LeafProofs.L23FieldMetricVertexCurve
import Yau.LeafProofs.L23FieldMetricParameterLocal
import Yau.LeafProofs.L23FieldMetricNormalData

/-! Actual free-vertex distance variations expressed in one common vertex chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem fieldNormalBranch_terminal_firstVariation
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y b : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target)
    (hb : y ∈ (chartAt (ComplexVector n) b).source) (w : ComplexVector n) :
    HasDerivAt (fun r => inducedDistance h q (fieldVertexCurve b y w r)^2)
      (2*realMetricInChart h b (chartPt b y)
        (fderiv ℝ (realChartChange c b) (chartPt c y)
          (normalFamilyPhase X (e.symm (chartPt c q,chartPt c y)) 1).2) w) 0 := by
  letI := manifold_realSmooth M
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let β := fieldVertexCurve b y w
  let Q : ℝ → ComplexVector n × ComplexVector n := fun r => (chartPt c q,chartPt c (β r))
  have hβ₀ : β 0 = y := fieldVertexCurve_zero b y hb w
  have hQ₀ : Q 0 = (chartPt c q,chartPt c y) := by change (chartPt c q,chartPt c (β 0)) = _; rw [hβ₀]
  have hQAt : ContDiffAt ℝ 2 Q 0 :=
    contDiffAt_const.prodMk ((fieldVertexCurve_coordinates_contDiffAt b c y hb hy w).of_le (by simp))
  obtain ⟨a,ha,hQ,hQmap⟩ := exists_parameter_interval Q e.target e.open_target hQAt (by rw [hQ₀]; exact hpair)
  have HD := normalEndpoint_distanceSq_hasDerivAt h hh c X e ha hε heq hinv hX
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩)
    (fun p hp => (hdata p hp).2.2.1) (fun p hp => (hdata p hp).2.2.2.1)
    (fun p hp => (hdata p hp).2.2.2.2.2) Q hQ hQmap
  have HdFirst : deriv (fun r => (Q r).1) 0 = 0 := deriv_const _ _
  have HdLast : deriv (fun r => (Q r).2) 0 = fderiv ℝ (realChartChange b c) (chartPt b y) w :=
    (fieldVertexCurve_coordinates_hasDerivAt b c y hb hy w).deriv
  rw [HdFirst,HdLast,hQ₀] at HD
  simp only [map_zero,mul_zero,sub_zero] at HD
  rw [realMetricInChart_coordinates_change_one_argument h c b y hy hb] at HD
  have hβsource : ∀ᶠ r in 𝓝 (0 : ℝ), β r ∈ (chartAt (ComplexVector n) c).source :=
    (fieldVertexCurve_contMDiffAt b y hb w).continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds (by rw [fieldVertexCurve_zero b y hb w]; exact hy))
  have hEq : (fun r => inducedDistance h q (β r)^2) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => inducedDistance h (chartInv c (Q r).1) (chartInv c (Q r).2)^2) := by
    filter_upwards [hβsource] with r hr
    have hqinv : chartInv c (chartPt c q) = q :=
      (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hq)
    have hβinv : chartInv c (chartPt c (β r)) = β r :=
      (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hr)
    change inducedDistance h q (β r)^2 = inducedDistance h (chartInv c (chartPt c q)) (chartInv c (chartPt c (β r)))^2
    rw [hqinv,hβinv]
  exact HD.congr_of_eventuallyEq hEq

theorem fieldNormalBranch_initial_firstVariation
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e)
    (q y b : M.Carrier) (hq : q ∈ (chartAt (ComplexVector n) c).source)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (hpair : (chartPt c q,chartPt c y) ∈ e.target)
    (hb : q ∈ (chartAt (ComplexVector n) b).source) (w : ComplexVector n) :
    HasDerivAt (fun r => inducedDistance h (fieldVertexCurve b q w r) y^2)
      (-2*realMetricInChart h b (chartPt b q)
        (fderiv ℝ (realChartChange c b) (chartPt c q) (e.symm (chartPt c q,chartPt c y)).2) w) 0 := by
  letI := manifold_realSmooth M
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  let β := fieldVertexCurve b q w
  let Q : ℝ → ComplexVector n × ComplexVector n := fun r => (chartPt c (β r),chartPt c y)
  have hβ₀ : β 0 = q := fieldVertexCurve_zero b q hb w
  have hQ₀ : Q 0 = (chartPt c q,chartPt c y) := by change (chartPt c (β 0),chartPt c y) = _; rw [hβ₀]
  have hQAt : ContDiffAt ℝ 2 Q 0 :=
    ((fieldVertexCurve_coordinates_contDiffAt b c q hb hq w).of_le (by simp)).prodMk contDiffAt_const
  obtain ⟨a,ha,hQ,hQmap⟩ := exists_parameter_interval Q e.target e.open_target hQAt (by rw [hQ₀]; exact hpair)
  have HD := normalEndpoint_distanceSq_hasDerivAt h hh c X e ha hε heq hinv hX
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩)
    (fun p hp => (hdata p hp).2.2.1) (fun p hp => (hdata p hp).2.2.2.1)
    (fun p hp => (hdata p hp).2.2.2.2.2) Q hQ hQmap
  have HdLast : deriv (fun r => (Q r).2) 0 = 0 := deriv_const _ _
  have HdFirst : deriv (fun r => (Q r).1) 0 = fderiv ℝ (realChartChange b c) (chartPt b q) w :=
    (fieldVertexCurve_coordinates_hasDerivAt b c q hb hq w).deriv
  rw [HdFirst,HdLast,hQ₀] at HD
  simp only [map_zero,zero_sub] at HD
  rw [realMetricInChart_coordinates_change_one_argument h c b q hq hb] at HD
  have hβsource : ∀ᶠ r in 𝓝 (0 : ℝ), β r ∈ (chartAt (ComplexVector n) c).source :=
    (fieldVertexCurve_contMDiffAt b q hb w).continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds (by rw [fieldVertexCurve_zero b q hb w]; exact hq))
  have hEq : (fun r => inducedDistance h (β r) y^2) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => inducedDistance h (chartInv c (Q r).1) (chartInv c (Q r).2)^2) := by
    filter_upwards [hβsource] with r hr
    have hyinv : chartInv c (chartPt c y) = y :=
      (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hy)
    have hβinv : chartInv c (chartPt c (β r)) = β r :=
      (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hr)
    change inducedDistance h (β r) y^2 = inducedDistance h (chartInv c (chartPt c (β r))) (chartInv c (chartPt c y))^2
    rw [hyinv,hβinv]
  convert! HD.congr_of_eventuallyEq hEq using 1
  ring

end Yau.LeafProofs.L23Aux
