import Yau.LeafProofs.L17BootstrapEvolutionBindingState
import Yau.LeafProofs.L17BootstrapEvolutionJets

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

/-- The actual N8 equation and the actual smooth parameter branch give joint
infinity for all spatial jets and time fields on the original closed slab.
No higher-time derivative, spatial infinity of u, or shorter interval is an input. -/
theorem actual_logdet_evolution_contDiffOn
    (P : UniformChartPartition g) (T : ℝ) (hT : 0<T) (hg : MetricSmooth g)
    (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (Jb : LocalHolderSpace ℝ P T (1/4) →L[ℝ] HolderSpace P T (1/4))
    (hJ : ∀ f, holderFun (Jb f)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P f)
    (u : SchauderSpace P T (1/4) hT)
    (hZ : ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr u‖<1)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hEq : scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr u=
      globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr Jb u)
    (p : P.centers) (z0 : ComplexVector n) (x : M.Carrier)
    (_hx : P.charts.chart p z0=x)
    (O : Set (ComplexVector n)) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hCoord : MapsTo (fun theta => z0+theta) O (ball 0 P.radius))
    (V : ComplexVector n → SchauderSpace P T (1/4) hT) (hV : ContDiffOn ℝ ∞ V O)
    (hShift : ∀ theta∈O, ∀ t : Time T,
      schauderFun (V theta) (x,t)=schauderFun u (P.charts.chart p (z0+theta),t)) :
    (∀ k, ContDiffOn ℝ ∞ (valueParameterJet P T (1/4) hT x V k) (O ×ˢ Icc 0 T)) ∧
    (∀ k, ContDiffOn ℝ ∞ (derivativeParameterJet P T (1/4) hT x V k) (O ×ˢ Icc 0 T)) ∧
    ContDiffOn ℝ ∞ (fun q : ComplexVector n × ℝ =>
      potentialFunction u (P.charts.chart p (z0+q.1)) q.2) (O ×ˢ Icc 0 T) := by
  obtain ⟨hContJ,hContB,hSpaceJ,hSpaceB,hTimeJets,hJ0,hB0⟩ :=
    actual_parameter_jet_family P T (1/4) hT x hO V hV
  have hState := actual_evolution_state_mapsTo u hSmall p z0 x hO hCoord V hV hShift
  have hEquation := actual_base_evolution_equation hg hTime (by norm_num : (0 : ℝ)≤1/4)
    (by norm_num : (1/4 : ℝ)≤1) hr Jb hJ u hZ hSmall hEq p z0 x hO hCoord V hV hShift
  have hRegular := contDiffOn_infty_of_evolution_spatial_jets
    (F := evolutionJetLogDet P.charts p z0) (D := evolutionPositiveJetDomain P.charts p z0)
    hO hConv hT hContJ hContB hSpaceJ hSpaceB hTimeJets
    (evolutionPositiveJetDomain_isOpen P.charts p z0) (evolutionJetLogDet_smooth P.charts p z0)
    hState hEquation
  refine ⟨hRegular.1,hRegular.2,(hRegular.1 0).congr ?_⟩
  rintro ⟨theta,tau⟩ hq
  simp only [potentialFunction,closedTimePath,valueParameterJet_zero,
    projIcc_of_mem hT.le hq.2]
  convert! (hShift theta hq.1 ⟨tau,hq.2⟩).symm using 1

end Yau.LeafProofs.L17BootstrapEvolutionBindingAux
