import Yau.LeafProofs.L17BootstrapMetricSmoothFrames

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricSmoothAux
open L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Local smoothness of the actual background-chart tensor coefficients gives
original metric-family smoothness in every fixed chart, on the same time set. -/
theorem metricFamilySmooth_of_local_pullback (P : UniformChartPartition g)
    (h : ℝ → HermitianField M) (I : Set ℝ)
    (hLocal : ∀ y : M.Carrier, ∃ p : P.centers, ∃ z : ComplexVector n, ∃ r : ℝ,
      0<r ∧ z∈ball 0 P.radius ∧ P.charts.chart p z=y ∧
      (∀ i j : Fin n, ContDiffOn ℝ ∞
        (fun a : ComplexVector n × ℝ => pullbackMatrix (h a.2) (P.charts.chart p) a.1 i j)
        (ball z r ×ˢ I))) : MetricFamilySmooth h I := by
  intro c a b q hq
  obtain ⟨p,z,r,hr,hz,hzq,hReg⟩ := hLocal (chartInv c q.1)
  let e := P.charts.chart p
  let psi : ComplexVector n → ComplexVector n := fun w => e.symm (chartInv c w)
  let O := inverseChartDomain e c
  have hzSource : z∈e.source := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hz))
  have hTarget : chartInv c q.1∈e.target := hzq ▸ e.map_source hzSource
  have hqO : q.1∈O := ⟨hq.1,hTarget⟩
  have hpsi : ContDiffOn ℝ ∞ psi O :=
    inverseChart_real_contDiffOn e (P.charts.inverse_differentiable p) c
  have hO : IsOpen O := inverseChartDomain_isOpen e c
  have hCoord : psi q.1=z := by
    change e.symm (chartInv c q.1)=z
    rw [←hzq]
    exact e.left_inv hzSource
  let V : Set (ComplexVector n) := O∩psi ⁻¹' ball z r
  have hV : IsOpen V := hpsi.continuousOn.isOpen_inter_preimage hO isOpen_ball
  have hqV : q.1∈V := by
    refine ⟨hqO,?_⟩
    change dist (psi q.1) z<r
    rw [hCoord,dist_self]
    exact hr
  have hMap : ContDiffOn ℝ ∞ (fun v : ComplexVector n × ℝ => (psi v.1,v.2)) (V ×ˢ I) :=
    (hpsi.comp contDiff_fst.contDiffOn (fun v hv => hv.1.1)).prodMk contDiff_snd.contDiffOn
  have hCoeff (i j : Fin n) : ContDiffOn ℝ ∞
      (fun v : ComplexVector n × ℝ => pullbackMatrix (h v.2) e (psi v.1) i j) (V ×ˢ I) :=
    (hReg i j).comp hMap (fun v hv => ⟨hv.1.2,hv.2⟩)
  have hEntry (d : RIdx n) (i : Fin n) : ContDiffOn ℝ ∞
      (fun v : ComplexVector n × ℝ => (fderiv ℂ psi v.1 (realVec d)) i) (V ×ˢ I) :=
    (inverseChart_derivative_component_contDiffOn e (P.charts.inverse_differentiable p) c d i).comp
      contDiff_fst.contDiffOn (fun v hv => hv.1.1)
  have hSum : ContDiffOn ℝ ∞ (fun v : ComplexVector n × ℝ => ∑ i, ∑ j,
      star ((fderiv ℂ psi v.1 (realVec a)) i)*
        (pullbackMatrix (h v.2) e (psi v.1) i j*((fderiv ℂ psi v.1 (realVec b)) j))) (V ×ˢ I) :=
    ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (Complex.conjCLE.contDiff.comp_contDiffOn (hEntry a i)).mul ((hCoeff i j).mul (hEntry b j))
  have hSmooth : ContDiffOn ℝ ∞ (fun v : ComplexVector n × ℝ => 2*(∑ i, ∑ j,
      star ((fderiv ℂ psi v.1 (realVec a)) i)*
        (pullbackMatrix (h v.2) e (psi v.1) i j*((fderiv ℂ psi v.1 (realVec b)) j))).re) (V ×ˢ I) :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn hSum)
  have hEqual : EqOn (fun v : ComplexVector n × ℝ => realMetricFn (h v.2) c v.1 a b)
      (fun v : ComplexVector n × ℝ => 2*(∑ i, ∑ j,
        star ((fderiv ℂ psi v.1 (realVec a)) i)*
          (pullbackMatrix (h v.2) e (psi v.1) i j*((fderiv ℂ psi v.1 (realVec b)) j))).re) (V ×ˢ I) := by
    intro v hv
    exact realMetricFn_eq_inverseChart_pullback (h v.2) e (P.charts.differentiable p)
      (P.charts.inverse_differentiable p) c hv.1.1 a b
  have hAt := (hSmooth.congr hEqual) q ⟨hqV,hq.2⟩
  apply hAt.mono_of_mem_nhdsWithin
  filter_upwards [mem_nhdsWithin_of_mem_nhds ((hV.prod isOpen_univ).mem_nhds
    (show q∈V ×ˢ (univ : Set ℝ) from ⟨hqV,mem_univ _⟩)),
    self_mem_nhdsWithin] with v hvV hvI
  exact ⟨hvV.1,hvI.2⟩

end Yau.LeafProofs.L17BootstrapMetricSmoothAux
