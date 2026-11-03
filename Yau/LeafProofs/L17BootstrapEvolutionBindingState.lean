import Yau.LeafProofs.L17BootstrapEvolutionBindingJetIdentity
import Yau.LeafProofs.L17BootstrapEvolutionBindingFiniteOperator
import Yau.LeafProofs.L17PotentialEquation
import Yau.LeafProofs.L17BootstrapEvolutionJetsProlong

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapEvolutionBindingAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapClosedSlabAux L17BootstrapJetEvaluationAux L17BootstrapEvolutionJetsAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- On its genuine spatial domain the finite-jet matrix is exactly the
background-minus-time-Ricci-plus-Levi expression. -/
theorem evolutionJetMatrix_eq_background_ricci (A : BoundedChartFamily g)
    (p : M.Carrier) (z0 : ComplexVector n) {s : State (ComplexVector n) 0}
    (hs : s∈evolutionSpatialDomain A z0) :
    evolutionJetMatrix A p z0 s=
      pullbackMatrix g (A.chart p) (z0+s.1.1)-
        (s.1.2 : ℂ) • pullbackRicci g (A.chart p) (z0+s.1.1)+
        leviHessianCLM n (s.2 ⟨2,by decide⟩) := by
  have hC2 : ContDiffAt ℝ 2 (A.backgroundLogDet p) (z0+s.1.1) :=
    ((A.backgroundLogDet_smooth p).contDiffAt (isOpen_ball.mem_nhds hs)).of_le (by simp)
  have hRic : pullbackRicci g (A.chart p) (z0+s.1.1)=
      -leviHessianCLM n (fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) (z0+s.1.1)) := by
    change -leviC (A.backgroundLogDet p) (z0+s.1.1)=_
    rw [leviC_eq_leviHessianCLM hC2]
  rw [hRic,smul_neg,sub_neg_eq_add]
  rfl

variable {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0<T}

theorem evolutionJetMatrix_state_eq_coordinate
    (u : SchauderSpace P T gamma hT) (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hCoord : MapsTo (fun theta => z0+theta) O (ball 0 P.radius))
    (V : ComplexVector n → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t))
    {theta : ComplexVector n} (htheta : theta∈O) (t : Time T) :
    evolutionJetMatrix P.charts p z0
      (stateJ (valueParameterJet P T gamma hT x V) 0 (theta,(t : ℝ)))=
      pullbackMatrix g (P.charts.chart p) (z0+theta)+
        coordinateMetricError u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩ := by
  have hJ2 := actual_parameter_jet_two_eq u p z0 x hO hCoord V hV hShift htheta t
  have hU : ContDiffAt ℝ 2 (chartFunction u p t) (z0+theta) :=
    (chartFunction_contDiffOn_two u p t).contDiffAt (isOpen_ball.mem_nhds (hCoord htheta))
  have hzBig : z0+theta∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) (hCoord htheta)
  have hBg : ContDiffAt ℝ 2 (P.charts.backgroundLogDet p) (z0+theta) :=
    ((P.charts.backgroundLogDet_smooth p).contDiffAt (isOpen_ball.mem_nhds hzBig)).of_le (by simp)
  have hLevi : leviHessianCLM n (hessianFun u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩)=
      leviC (chartFunction u p t) (z0+theta) := by
    rw [←(chartFunction_hasSecondFDerivAt u p t (hCoord htheta)).fderiv]
    exact (leviC_eq_leviHessianCLM hU).symm
  change pullbackMatrix g (P.charts.chart p) (z0+theta)+
    (t : ℂ) • leviHessianCLM n (fderiv ℝ (fderiv ℝ (P.charts.backgroundLogDet p)) (z0+theta))+
    leviHessianCLM n (valueParameterJet P T gamma hT x V 2 (theta,(t : ℝ)))=_
  rw [hJ2,hLevi,←leviC_eq_leviHessianCLM hBg,coordinateMetricError,matrixRealScalar_eq_complexScalar]
  abel

/-- Original N8 smallness gives genuine positive real determinants at every
actual state, including both closed-time endpoints. -/
theorem actual_evolution_state_mapsTo
    (u : SchauderSpace P T gamma hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hCoord : MapsTo (fun theta => z0+theta) O (ball 0 P.radius))
    (V : ComplexVector n → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t)) :
    MapsTo (stateJ (valueParameterJet P T gamma hT x V) 0) (O ×ˢ Icc 0 T)
      (evolutionPositiveJetDomain P.charts p z0) := by
  rintro ⟨theta,tau⟩ hq
  let t : Time T := ⟨tau,hq.2⟩
  have hzBig : z0+theta∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) (hCoord hq.1)
  refine ⟨⟨hzBig,?_⟩,?_⟩
  · change 0<(evolutionJetMatrix P.charts p z0
      (stateJ (valueParameterJet P T gamma hT x V) 0 (theta,(t : ℝ)))).det.re
    rw [evolutionJetMatrix_state_eq_coordinate u p z0 x hO hCoord V hV hShift hq.1 t]
    exact (Complex.pos_iff.mp (coordinateMetric_half_double u hSmall
      ⟨p,(⟨z0+theta,hCoord hq.1⟩,t)⟩).1.det_pos).1
  · exact P.charts.backgroundLogDet_det_pos p hzBig

/-- The original N8 equation supplies the actual scalar finite-jet evolution,
with no caller PDE or higher-time derivative oracle. -/
theorem actual_base_evolution_equation
    (hg : MetricSmooth g) (hTime : T≤P.radius^2) (hgamma : 0≤gamma) (hgamma1 : gamma≤1)
    (hr : P.radius≤1)
    (Jb : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ f, holderFun (Jb f)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P f)
    (u : SchauderSpace P T gamma hT)
    (hZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma hgamma1 hr u‖<1)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hEq : scalarParabolicCLM P T gamma hT hTime hgamma1 hr u=
      globalNonlinearMap P T gamma hT hTime hgamma hgamma1 hr Jb u)
    (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hCoord : MapsTo (fun theta => z0+theta) O (ball 0 P.radius))
    (V : ComplexVector n → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t)) :
    ∀ q∈O ×ˢ Icc 0 T,
      derivativeParameterJet P T gamma hT x V 0 q=
        evolutionJetLogDet P.charts p z0 (stateJ (valueParameterJet P T gamma hT x V) 0 q) := by
  rintro ⟨theta,tau⟩ hq
  let t : Time T := ⟨tau,hq.2⟩
  let y := P.charts.chart p (z0+theta)
  have hB := actual_parameter_time_zero_eq u p z0 x hO V hV hShift hq.1 t
  have hOriginal := potentialFunction_hasDerivWithinAt_of_equation P T gamma hT
    hTime hgamma hgamma1 hr hg Jb hJ u hZ hSmall hEq y t
  have hNative := schauderFun_hasDerivWithinAt u y t
  change HasDerivWithinAt (potentialFunction u y) (timeFun u (y,t)) (Icc (0 : ℝ) T) (t : ℝ) at hNative
  have hLog : timeFun u (y,t)=
      Real.log ((gMat (potentialFlowField hg u hSmall (t : ℝ)) y).det.re/(gMat g y).det.re) :=
    (hNative.derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property)).symm.trans
      (hOriginal.derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property))
  rw [gMat_potentialFlowField] at hLog
  calc
    _ = timeFun u (y,t) := hB
    _ = Real.log ((potentialMetricMatrix u (y,t)).det.re/(gMat g y).det.re) := hLog
    _ = Real.log ((pullbackMatrix g (P.charts.chart p) (z0+theta)+
        coordinateMetricError u ⟨p,(⟨z0+theta,hCoord hq.1⟩,t)⟩).det.re/
      (pullbackMatrix g (P.charts.chart p) (z0+theta)).det.re) :=
      congrArg Real.log (coordinateMetricMatrix_determinant_ratio hg u
        ⟨p,(⟨z0+theta,hCoord hq.1⟩,t)⟩).symm
    _ = _ := by
      unfold evolutionJetLogDet evolutionJetDet evolutionJetBackgroundDet
      rw [evolutionJetMatrix_state_eq_coordinate u p z0 x hO hCoord V hV hShift hq.1 t]
      rfl

end Yau.LeafProofs.L17BootstrapEvolutionBindingAux
