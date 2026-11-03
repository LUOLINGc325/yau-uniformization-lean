import Yau.LeafProofs.L17BootstrapJetEvaluation

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapEvolutionBindingAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapClosedSlabAux L17BootstrapJetEvaluationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0<T}

/-- Literal shifted values identify the actual zero parameter jet. -/
theorem actual_parameter_jet_zero_eq
    (u : SchauderSpace P T gamma hT) (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (V : ComplexVector n → SchauderSpace P T gamma hT)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t))
    {theta : ComplexVector n} (htheta : theta∈O) (t : Time T) :
    valueParameterJet P T gamma hT x V 0 (theta,(t : ℝ))=
      chartFunction u p t (z0+theta) := by
  simp only [valueParameterJet_zero,projIcc_of_mem hT.le t.property]
  exact hShift theta htheta t

/-- Uniqueness of the actual spatial derivative identifies J1 with the stored gradient. -/
theorem actual_parameter_jet_one_eq
    (u : SchauderSpace P T gamma hT) (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hCoord : MapsTo (fun theta => z0+theta) O (ball 0 P.radius))
    (V : ComplexVector n → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t))
    {theta : ComplexVector n} (htheta : theta∈O) (t : Time T) :
    valueParameterJet P T gamma hT x V 1 (theta,(t : ℝ))=
      gradientFun u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩ := by
  have hFamily := actual_parameter_jet_family P T gamma hT x hO V hV
  have hJ := hFamily.2.2.1 0 theta htheta (t : ℝ) t.property
  have hNative := (chartFunction_hasFDerivAt u p t (hCoord htheta)).comp theta
    ((hasFDerivAt_id theta).const_add z0)
  have hEqual : (fun y => valueParameterJet P T gamma hT x V 0 (y,(t : ℝ)))
      =ᶠ[𝓝 theta] (fun y => chartFunction u p t (z0+y)) := by
    filter_upwards [hO.mem_nhds htheta] with y hy
    exact actual_parameter_jet_zero_eq u p z0 x V hShift hy t
  have hOther : HasFDerivAt (fun y => valueParameterJet P T gamma hT x V 0 (y,(t : ℝ)))
      (gradientFun u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩) theta := by
    apply HasFDerivAt.congr_of_eventuallyEq _ hEqual
    convert! hNative using 1 <;> simp only [Function.comp_def,ContinuousLinearMap.comp_id]
  exact hJ.unique hOther

/-- J2 is the original stored Hessian, obtained by differentiating the actual
J1 identity on the open parameter domain; no third derivative of u is used. -/
theorem actual_parameter_jet_two_eq
    (u : SchauderSpace P T gamma hT) (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hCoord : MapsTo (fun theta => z0+theta) O (ball 0 P.radius))
    (V : ComplexVector n → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t))
    {theta : ComplexVector n} (htheta : theta∈O) (t : Time T) :
    valueParameterJet P T gamma hT x V 2 (theta,(t : ℝ))=
      hessianFun u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩ := by
  have hFamily := actual_parameter_jet_family P T gamma hT x hO V hV
  have hJ := hFamily.2.2.1 1 theta htheta (t : ℝ) t.property
  have hNative := (chartFunction_hasSecondFDerivAt u p t (hCoord htheta)).comp theta
    ((hasFDerivAt_id theta).const_add z0)
  have hEqual : (fun y => valueParameterJet P T gamma hT x V 1 (y,(t : ℝ)))
      =ᶠ[𝓝 theta] (fun y => fderiv ℝ (chartFunction u p t) (z0+y)) := by
    filter_upwards [hO.mem_nhds htheta] with y hy
    rw [actual_parameter_jet_one_eq u p z0 x hO hCoord V hV hShift hy t]
    exact (chartFunction_hasFDerivAt u p t (hCoord hy)).fderiv.symm
  have hOther : HasFDerivAt (fun y => valueParameterJet P T gamma hT x V 1 (y,(t : ℝ)))
      (hessianFun u ⟨p,(⟨z0+theta,hCoord htheta⟩,t)⟩) theta := by
    apply HasFDerivAt.congr_of_eventuallyEq _ hEqual
    convert! hNative using 1 <;> simp only [Function.comp_def,ContinuousLinearMap.comp_id]
  exact hJ.unique hOther

/-- The real closed-time derivative B0 equals the native time field at both
endpoints as well as in the interior. -/
theorem actual_parameter_time_zero_eq
    (u : SchauderSpace P T gamma hT) (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    (V : ComplexVector n → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t))
    {theta : ComplexVector n} (htheta : theta∈O) (t : Time T) :
    derivativeParameterJet P T gamma hT x V 0 (theta,(t : ℝ))=
      timeFun u (P.charts.chart p (z0+theta),t) := by
  have hFamily := actual_parameter_jet_family P T gamma hT x hO V hV
  have hJ := hFamily.2.2.2.2.1 0 theta htheta (t : ℝ) t.property
  have hEqual : ∀ tau∈Icc (0 : ℝ) T,
      schauderFun u (closedTimePath T hT (P.charts.chart p (z0+theta)) tau)=
        valueParameterJet P T gamma hT x V 0 (theta,tau) := by
    intro tau htau
    simpa only [valueParameterJet_zero,closedTimePath,projIcc_of_mem hT.le htau] using
      (hShift theta htheta ⟨tau,htau⟩).symm
  have hJ' := hJ.congr_of_mem hEqual t.property
  have hNative := schauderFun_hasDerivWithinAt u (P.charts.chart p (z0+theta)) t
  exact (hJ'.derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property)).symm.trans
    (hNative.derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property))

end Yau.LeafProofs.L17BootstrapEvolutionBindingAux
