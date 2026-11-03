import Yau.LeafProofs.L17ParabolicOperatorCoefficients
import Yau.LeafProofs.L17ScalarChartOperator

open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicOperatorAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}

/-- Genuine C2 follows from the recovered native first and second derivatives. -/
theorem chartFunction_contDiffOn_two (u : SchauderSpace P T gamma hT)
    (p : P.centers) (t : Time T) :
    ContDiffOn ℝ 2 (chartFunction u p t) (ball (0 : ComplexVector n) P.radius) := by
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ (chartFunction u p t)))
      (ball (0 : ComplexVector n) P.radius) := by
    apply (chartHessian_continuousOn u p t).congr
    intro z hz
    simpa only [chartHessian,dite_eq_left hz] using (chartFunction_hasSecondFDerivAt u p t hz).fderiv
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (chartFunction u p t))
      (ball (0 : ComplexVector n) P.radius) := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := (0 : ℕ∞ω)) isOpen_ball).mpr
    refine ⟨fun z hz => (chartFunction_hasSecondFDerivAt u p t hz).differentiableAt.differentiableWithinAt,by simp,?_⟩
    simpa only [contDiffOn_zero] using hH
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := (1 : ℕ∞ω)) isOpen_ball).mpr
  exact ⟨fun z hz => (chartFunction_hasFDerivAt u p t hz).differentiableAt.differentiableWithinAt,by simp,hD⟩

/-- Transfer actual selected-chart regularity to the native chart used by laplacian. -/
theorem native_contDiffAt_of_background
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (f : M.Carrier → ℝ) {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ContDiffAt ℝ 2 (fun w => f (e w)) z) :
    ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z)) := by
  let a := e z
  let z0 := chartPt a a
  have hInv0 : chartInv a z0 = a := (extChartAt (ComplexModel n) a).left_inv (mem_extChartAt_source a)
  have hmem : z0 ∈ inverseChartDomain e a := by
    refine ⟨mem_extChartAt_target a,?_⟩
    change chartInv a z0 ∈ e.target
    rw [hInv0]
    exact e.map_source hz
  have hnear := (inverseChartDomain_isOpen e a).mem_nhds hmem
  have hInv : ContDiffAt ℝ 2 (fun y => e.symm (chartInv a y)) z0 :=
    ((inverseChart_real_contDiffOn e hei a).contDiffAt hnear).of_le (by simp)
  have hInvz : e.symm (chartInv a z0) = z := by rw [hInv0]; exact e.left_inv hz
  have hf' : ContDiffAt ℝ 2 (fun w => f (e w)) (e.symm (chartInv a z0)) := hInvz.symm ▸ hf
  apply (hf'.comp z0 hInv).congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  change f (chartInv a w) = f (e (e.symm (chartInv a w)))
  exact congrArg f (e.right_inv hw.2).symm

theorem selected_chart_laplacian (u : SchauderSpace P T gamma hT) (p : P.centers)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    laplacian g (fun y => schauderFun u (y,t)) (P.charts.chart p z) =
      hessianContractionCLM n (chartCoefficient P.charts p z) (hessianFun u ⟨p,(z,t)⟩) := by
  have hz : (z : ComplexVector n) ∈ (P.charts.chart p).source :=
    P.charts.closedBall_source p (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hf := (chartFunction_contDiffOn_two u p t).contDiffAt (isOpen_ball.mem_nhds z.property)
  have hNative := native_contDiffAt_of_background (P.charts.chart p) (P.charts.inverse_differentiable p)
    (fun y => schauderFun u (y,t)) hz hf
  rw [laplacian_eq_backgroundChart_scalarSymbol g (P.charts.chart p) (P.charts.differentiable p)
    (P.charts.inverse_differentiable p) _ hz hNative]
  change realHessianContraction (chartCoefficient P.charts p z) (chartFunction u p t) z = _
  rw [← hessianContractionCLM_eq_actual,(chartFunction_hasSecondFDerivAt u p t z.property).fderiv]

def actualLaplacian (u : SchauderSpace P T gamma hT) (q : Cylinder M T) : ℝ :=
  laplacian g (fun y => schauderFun u (y,q.2)) q.1

theorem exists_selected_chart (P : UniformChartPartition g) (x : M.Carrier) :
    ∃ p : P.centers, ∃ z : ↥(ball (0 : ComplexVector n) P.radius), P.charts.chart p z = x := by
  obtain ⟨p,hp,z,hz,hzx⟩ := P.covers x
  have hz' : z ∈ ball (0 : ComplexVector n) P.radius :=
    (ball_subset_ball (by linarith only [P.radius_pos] : P.radius/4 ≤ P.radius)) hz
  exact ⟨⟨p,hp⟩,⟨z,hz'⟩,hzx⟩

/-- Every actual time slice is C2 at every native manifold-chart point. -/
theorem actualFunction_native_contDiffAt (u : SchauderSpace P T gamma hT)
    (x : M.Carrier) (t : Time T) :
    ContDiffAt ℝ 2 (inChart x (fun y => schauderFun u (y,t))) (chartPt x x) := by
  obtain ⟨p,z,hzx⟩ := exists_selected_chart P x
  have hz : (z : ComplexVector n) ∈ (P.charts.chart p).source :=
    P.charts.closedBall_source p (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hf := (chartFunction_contDiffOn_two u p t).contDiffAt (isOpen_ball.mem_nhds z.property)
  have h := native_contDiffAt_of_background (P.charts.chart p) (P.charts.inverse_differentiable p)
    (fun y => schauderFun u (y,t)) hz hf
  simpa only [hzx] using h

def chartView (P : UniformChartPartition g) (p : P.centers) : Set M.Carrier :=
  (P.charts.chart p).target ∩ (P.charts.chart p).symm ⁻¹' ball (0 : ComplexVector n) P.radius

theorem chartView_isOpen (P : UniformChartPartition g) (p : P.centers) : IsOpen (chartView P p) :=
  (P.charts.chart p).symm.continuousOn.isOpen_inter_preimage (P.charts.chart p).open_target isOpen_ball

theorem actualLaplacian_continuousOn_view (u : SchauderSpace P T gamma hT) (p : P.centers) :
    ContinuousOn (actualLaplacian u) (chartView P p ×ˢ (univ : Set (Time T))) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let S := chartView P p ×ˢ (univ : Set (Time T))
  have hCoord : Continuous (fun q : S => (P.charts.chart p).symm q.val.1) :=
    (P.charts.chart p).symm.continuousOn.comp_continuous (continuous_fst.comp continuous_subtype_val)
      (fun q => q.property.1.1)
  have hLift : Continuous (fun q : S => (⟨p,(⟨(P.charts.chart p).symm q.val.1,q.property.1.2⟩,q.val.2)⟩ : LocalCylinder P T)) :=
    continuous_sigmaMk.comp ((hCoord.subtype_mk _).prodMk (continuous_snd.comp continuous_subtype_val))
  have hCoef : Continuous (fun q : S => chartCoefficient P.charts p ((P.charts.chart p).symm q.val.1)) :=
    (chartCoefficient_smooth P.charts p).continuousOn.comp_continuous hCoord
      (fun q => (ball_subset_ball P.radius_lt.le) q.property.1.2)
  have hH := (hessianFun_continuous u).comp hLift
  have hCtr := ((hessianContractionCLM n).continuous.comp hCoef).clm_apply hH
  convert hCtr using 1
  funext q
  have heq : P.charts.chart p ((P.charts.chart p).symm q.val.1) = q.val.1 :=
    (P.charts.chart p).right_inv q.property.1.1
  have h := selected_chart_laplacian u p ⟨(P.charts.chart p).symm q.val.1,q.property.1.2⟩ q.val.2
  simpa only [Set.domRestrict_apply,actualLaplacian,Function.comp_apply,heq] using h

/-- Joint continuity is proved on the real closed manifold-time cylinder. -/
theorem actualLaplacian_continuous (u : SchauderSpace P T gamma hT) : Continuous (actualLaplacian u) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨p,z,hzx⟩ := exists_selected_chart P q.1
  have hz : (z : ComplexVector n) ∈ (P.charts.chart p).source :=
    P.charts.closedBall_source p (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hq : q.1 ∈ chartView P p := by
    refine ⟨?_,?_⟩
    · rw [← hzx]
      exact (P.charts.chart p).map_source hz
    · change (P.charts.chart p).symm q.1 ∈ ball (0 : ComplexVector n) P.radius
      rw [← hzx,(P.charts.chart p).left_inv hz]
      exact z.property
  exact (actualLaplacian_continuousOn_view u p).continuousAt
    (((chartView_isOpen P p).prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)

end Yau.LeafProofs.L17ParabolicOperatorAux
