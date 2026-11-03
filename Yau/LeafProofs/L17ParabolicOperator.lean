import Yau.LeafProofs.L17ParabolicOperatorBounds

open Set Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17ParabolicOperatorAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
  (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1)


def scalarLaplacianElement (u : SchauderSpace P T gamma hT) : HolderSpace P T gamma :=
  ofBounds P T gamma (actualLaplacian u) (actualLaplacian_continuous u)
    (laplacianBudget P.charts gamma*‖u‖) (laplacianBudget P.charts gamma*‖u‖)
    (actualLaplacian_holder_bounds hTime hgamma hr u).1 (actualLaplacian_holder_bounds hTime hgamma hr u).2

theorem scalarLaplacianElement_value (u : SchauderSpace P T gamma hT) :
    holderFun (scalarLaplacianElement P T gamma hT hTime hgamma hr u) = actualLaplacian u := rfl

theorem scalarLaplacianElement_norm_le (u : SchauderSpace P T gamma hT) :
    ‖scalarLaplacianElement P T gamma hT hTime hgamma hr u‖ ≤ laplacianBudget P.charts gamma*‖u‖ := by
  have hK : 0 ≤ laplacianBudget P.charts gamma*‖u‖ :=
    mul_nonneg (zero_le_one.trans (laplacianBudget_ge_one _ _)) (norm_nonneg _)
  simpa only [max_self,scalarLaplacianElement] using ofBounds_norm_le P T gamma (actualLaplacian u) (actualLaplacian_continuous u)
    _ _ hK hK (actualLaplacian_holder_bounds hTime hgamma hr u).1 (actualLaplacian_holder_bounds hTime hgamma hr u).2

def scalarLaplacianLinearMap : SchauderSpace P T gamma hT →ₗ[ℝ] HolderSpace P T gamma where
  toFun := scalarLaplacianElement P T gamma hT hTime hgamma hr
  map_add' u v := by
    apply holderFun_injective P T gamma
    funext q
    obtain ⟨p,z,hzx⟩ := exists_selected_chart P q.1
    change actualLaplacian (u+v) q = actualLaplacian u q+actualLaplacian v q
    change laplacian g (fun y => schauderFun (u+v) (y,q.2)) q.1 =
      laplacian g (fun y => schauderFun u (y,q.2)) q.1+laplacian g (fun y => schauderFun v (y,q.2)) q.1
    rw [← hzx,selected_chart_laplacian,selected_chart_laplacian,selected_chart_laplacian]
    have hH : hessianFun (u+v) ⟨p,(z,q.2)⟩ = hessianFun u ⟨p,(z,q.2)⟩+hessianFun v ⟨p,(z,q.2)⟩ :=
      congrArg (fun f : BoundedContinuousFunction (LocalCylinder P T) (D2 n) => f ⟨p,(z,q.2)⟩)
        ((hessianCLM P T gamma hT).map_add u v)
    rw [hH,map_add]
  map_smul' c u := by
    apply holderFun_injective P T gamma
    funext q
    obtain ⟨p,z,hzx⟩ := exists_selected_chart P q.1
    change actualLaplacian (SMul.smul (M := ℝ) (α := SchauderSpace P T gamma hT) c u) q = c*actualLaplacian u q
    change laplacian g (fun y => schauderFun (SMul.smul (M := ℝ) (α := SchauderSpace P T gamma hT) c u) (y,q.2)) q.1 =
      c*laplacian g (fun y => schauderFun u (y,q.2)) q.1
    rw [← hzx,selected_chart_laplacian,selected_chart_laplacian]
    have hH : hessianFun (SMul.smul (M := ℝ) (α := SchauderSpace P T gamma hT) c u) ⟨p,(z,q.2)⟩ = c • hessianFun u ⟨p,(z,q.2)⟩ :=
      congrArg (fun f : BoundedContinuousFunction (LocalCylinder P T) (D2 n) => f ⟨p,(z,q.2)⟩)
        ((hessianCLM P T gamma hT).map_smul c u)
    rw [hH,map_smul]
    rfl

def scalarLaplacianCLM : SchauderSpace P T gamma hT →L[ℝ] HolderSpace P T gamma :=
  (scalarLaplacianLinearMap P T gamma hT hTime hgamma hr).mkContinuous (laplacianBudget P.charts gamma)
    (scalarLaplacianElement_norm_le P T gamma hT hTime hgamma hr)

theorem scalarLaplacianCLM_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    holderFun (scalarLaplacianCLM P T gamma hT hTime hgamma hr u) q =
      laplacian g (fun y => schauderFun u (y,q.2)) q.1 := rfl

theorem scalarLaplacianCLM_opNorm_le :
    ‖scalarLaplacianCLM P T gamma hT hTime hgamma hr‖ ≤ laplacianBudget P.charts gamma :=
  ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (laplacianBudget_ge_one _ _))
    (scalarLaplacianElement_norm_le P T gamma hT hTime hgamma hr)

def scalarParabolicCLM : SchauderSpace P T gamma hT →L[ℝ] HolderSpace P T gamma :=
  timeHolderCLM P T gamma hT-scalarLaplacianCLM P T gamma hT hTime hgamma hr

theorem scalarParabolicCLM_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    holderFun (scalarParabolicCLM P T gamma hT hTime hgamma hr u) q = timeFun u q-
      laplacian g (fun y => schauderFun u (y,q.2)) q.1 := rfl

theorem scalarParabolicCLM_opNorm_le :
    ‖scalarParabolicCLM P T gamma hT hTime hgamma hr‖ ≤ 1+laplacianBudget P.charts gamma :=
  (norm_sub_le _ _).trans (add_le_add (timeHolderCLM_opNorm_le P T gamma hT)
    (scalarLaplacianCLM_opNorm_le P T gamma hT hTime hgamma hr))

/-- One constant precedes the partition radius, time, and input function. -/
theorem exists_uniform_parabolic_operator_budget (A : BoundedChartFamily g) (gamma : ℝ)
    (_hgamma0 : 0 < gamma) (hgamma1 : gamma < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : UniformChartPartition g), P.charts = A →
      ∀ (T : ℝ) (hT : 0 < T) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1),
        ‖scalarLaplacianCLM P T gamma hT hTime hgamma1.le hr‖ ≤ C ∧
        ‖scalarParabolicCLM P T gamma hT hTime hgamma1.le hr‖ ≤ C := by
  refine ⟨1+laplacianBudget A gamma,?_,?_⟩
  · have h := laplacianBudget_ge_one A gamma
    linarith
  · intro P hPA T hT hTime hr
    have hL := scalarLaplacianCLM_opNorm_le P T gamma hT hTime hgamma1.le hr
    have hP := scalarParabolicCLM_opNorm_le P T gamma hT hTime hgamma1.le hr
    rw [hPA] at hL hP
    exact ⟨hL.trans (by linarith),hP⟩

end Yau.LeafProofs.L17ParabolicOperatorAux
