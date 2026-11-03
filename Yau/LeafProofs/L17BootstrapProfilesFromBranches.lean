import Yau.LeafProofs.L17BootstrapEvolutionBinding
import Yau.LeafProofs.L17BootstrapFlowSmooth
import Yau.LeafProofs.L17BootstrapPatchBounds

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapProfilesFromBranchesAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapPatchAux L17BootstrapJetEvaluationAux
open L17BootstrapEvolutionBindingAux L17BootstrapFlowSmoothAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- The actual patch radii imply the required coordinate containment directly
by the norm triangle inequality, without a cutoff translation identity. -/
theorem patch_shift_ball_mapsTo {P : UniformChartPartition g} {y : M.Carrier}
    (D : BootstrapPatch P y) {r : ℝ} (hr : r≤D.smallRadius/2) :
    MapsTo (fun theta => D.coord+theta) (ball 0 r) (ball 0 P.radius) := by
  intro theta htheta
  have hz : ‖D.coord‖<P.radius/4 := by
    simpa only [mem_ball,dist_zero_right] using D.coord_mem
  have ht : ‖theta‖<r := by simpa only [mem_ball,dist_zero_right] using htheta
  rw [mem_ball,dist_zero_right]
  exact (norm_add_le _ _).trans_lt (by linarith only [hz,ht,hr,D.smallRadius_le_radius,P.radius_pos])

/-- Actual local smooth parameter branches and their literal value shifts
produce both original smoothness conclusions on the same full closed slab. -/
theorem potentialFlow_smooth_of_actual_shift_branches
    (P : UniformChartPartition g) (T : ℝ) (hT : 0<T) (hg : MetricSmooth g)
    (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (Jb : LocalHolderSpace ℝ P T (1/4) →L[ℝ] HolderSpace P T (1/4))
    (hJ : ∀ f, holderFun (Jb f)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P f)
    (u : SchauderSpace P T (1/4) hT)
    (hZ : ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr u‖<1)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hEq : scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr u=
      globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr Jb u)
    (hBranches : ∀ y : M.Carrier, ∃ D : BootstrapPatch P y, ∃ r : ℝ,
      0<r ∧ r≤D.smallRadius/2 ∧
      ∃ V : ComplexVector n → SchauderSpace P T (1/4) hT,
        ContDiffOn ℝ ∞ V (ball 0 r) ∧
        ∀ theta∈ball 0 r, ∀ t : Time T,
          schauderFun (V theta) (y,t)=schauderFun u (P.charts.chart D.center (D.coord+theta),t)) :
    SmoothSpaceTime (potentialFunction u) (Icc (0 : ℝ) T) ∧
      MetricFamilySmooth (potentialFlowField hg u hSmall) (Icc (0 : ℝ) T) := by
  apply potentialFlow_smooth_of_local_jets hg hTime hr u hSmall
  intro y
  obtain ⟨D,r,hr0,hrSmall,V,hV,hShift⟩ := hBranches y
  have hCoord := patch_shift_ball_mapsTo D hrSmall
  have hz : D.coord∈ball (0 : ComplexVector n) P.radius :=
    (ball_subset_ball (by linarith only [P.radius_pos] : P.radius/4≤P.radius)) D.coord_mem
  have hReg := actual_logdet_evolution_contDiffOn P T hT hg hTime hr Jb hJ u hZ hSmall hEq
    D.center D.coord y D.center_eq (ball 0 r) isOpen_ball (convex_ball 0 r) hCoord V hV hShift
  let f : ComplexVector n × ℝ → ℝ :=
    fun q => potentialFunction u (P.charts.chart D.center (D.coord+q.1)) q.2
  let Q : ComplexVector n × ℝ → D2 n := valueParameterJet P T (1/4) hT y V 2
  refine ⟨D.center,D.coord,r,hr0,hz,D.center_eq,hCoord,f,Q,hReg.2.2,?_,?_,?_⟩
  · convert! hReg.1 2 using 1
  · intro q _hq
    rfl
  · intro theta htheta t
    exact actual_parameter_jet_two_eq u D.center D.coord y isOpen_ball hCoord V hV hShift htheta t

end Yau.LeafProofs.L17BootstrapProfilesFromBranchesAux
