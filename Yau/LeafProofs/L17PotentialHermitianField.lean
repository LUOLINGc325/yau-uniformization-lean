import Yau.LeafProofs.L17MetricMatrixPositivity
import Yau.LeafProofs.L17HermitianMatrixAssembly
import Yau.LeafProofs.L17NonlinearPointValues

open Set Metric
open scoped Matrix ComplexOrder ContDiff Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17HermitianMatrixAssemblyAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ} {hT : 0<T}

def potentialFunction (u : SchauderSpace P T γ hT) (x : M.Carrier) (t : ℝ) : ℝ :=
  schauderFun u (closedTimePath T hT x t)

theorem potentialFunction_value (u : SchauderSpace P T γ hT) (q : Cylinder M T) :
    potentialFunction u q.1 (q.2 : ℝ)=schauderFun u q := by
  simp only [potentialFunction,closedTimePath,projIcc_of_mem hT.le q.2.property]

theorem potentialFunction_initial (u : SchauderSpace P T γ hT) (x : M.Carrier) :
    potentialFunction u x 0=0 := by
  rw [show potentialFunction u x 0=potentialFunction u x
    ((⟨0,⟨le_refl 0,hT.le⟩⟩ : Time T) : ℝ) from rfl,
    potentialFunction_value u (x,⟨0,⟨le_refl 0,hT.le⟩⟩),schauderFun_initial]

def potentialTimeField (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (t : Time T) : HermitianField M :=
  hermitianFieldOfMatrices (fun x => potentialMetricMatrix u (x,t))
    (fun x => (potentialMetricMatrix_comparison hg u hSmall (x,t)).1)

theorem gMat_potentialTimeField (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (t : Time T) (x : M.Carrier) :
    gMat (potentialTimeField hg u hSmall t) x=potentialMetricMatrix u (x,t) :=
  gMat_hermitianFieldOfMatrices _ _ x

def potentialFlowField (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (t : ℝ) : HermitianField M :=
  if ht : t∈Icc (0:ℝ) T then potentialTimeField hg u hSmall ⟨t,ht⟩ else g

theorem gMat_potentialFlowField (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (t : Time T) (x : M.Carrier) :
    gMat (potentialFlowField hg u hSmall (t : ℝ)) x=potentialMetricMatrix u (x,t) := by
  rw [potentialFlowField,dite_eq_left t.property,gMat_potentialTimeField]

theorem potentialFlowField_initial (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹) :
    potentialFlowField hg u hSmall 0=g := by
  apply hermitianField_ext
  intro x
  rw [show (0:ℝ)=((⟨0,⟨le_refl 0,hT.le⟩⟩ : Time T) : ℝ) from rfl,
    gMat_potentialFlowField,potentialMetricMatrix_initial]

theorem potentialFlowField_matrix_identity (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (t : Time T) (x : M.Carrier) :
    gMat (potentialFlowField hg u hSmall (t : ℝ)) x=
      gMat g x-(t : ℂ) • ricci g x+levi (fun y => potentialFunction u y (t : ℝ)) x := by
  have hF : (fun y => potentialFunction u y (t : ℝ))=fun y => schauderFun u (y,t) :=
    funext fun y => potentialFunction_value u (y,t)
  rw [gMat_potentialFlowField,hF,potentialMetricMatrix]
  abel

theorem potentialFlowField_comparison (hg : MetricSmooth g) (u : SchauderSpace P T γ hT)
    (hSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (t : Time T) (x : M.Carrier) :
    (gMat (potentialFlowField hg u hSmall (t : ℝ)) x-(1/2 : ℂ) • gMat g x).PosSemidef ∧
      ((2 : ℂ) • gMat g x-gMat (potentialFlowField hg u hSmall (t : ℝ)) x).PosSemidef := by
  rw [gMat_potentialFlowField]
  exact (potentialMetricMatrix_comparison hg u hSmall (x,t)).2

end Yau.LeafProofs.L17Aux
