import Yau.LeafProofs.L17BackgroundLogDetJets
import Yau.LeafProofs.L17NormalizedPotential

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux L17LocalHolderBanachAlgebraAux
local instance ricciHolderTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def backgroundLogDetHessian (A : BoundedChartFamily g) (p : M.Carrier) (z : ComplexVector n) : D2 n :=
  fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) z

theorem exists_backgroundLogDetHessian_budget (A : BoundedChartFamily g) :
    ∃ C : ℝ,1≤C ∧ ∀ p z,z∈ball (0 : ComplexVector n) A.radius →
      ‖backgroundLogDetHessian A p z‖≤C ∧ ‖fderiv ℝ (backgroundLogDetHessian A p) z‖≤C := by
  obtain ⟨C,hC,hb⟩ := A.backgroundLogDet_hessian_uniformJetBounds 1
  refine ⟨C,hC,?_⟩
  intro p z hz
  exact ⟨by simpa only [backgroundLogDetHessian,norm_iteratedFDeriv_zero] using hb p z hz 0 (by omega),
    by
      change ‖fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) w) z‖≤C
      simpa only [norm_iteratedFDeriv_one] using hb p z hz 1 (by omega)⟩

def backgroundLogDetHessianBudget (A : BoundedChartFamily g) : ℝ :=
  Classical.choose (exists_backgroundLogDetHessian_budget A)

theorem backgroundLogDetHessianBudget_ge_one (A : BoundedChartFamily g) :
    1≤backgroundLogDetHessianBudget A :=
  (Classical.choose_spec (exists_backgroundLogDetHessian_budget A)).1

theorem backgroundLogDetHessian_bounds (A : BoundedChartFamily g) (p : M.Carrier)
    {z : ComplexVector n} (hz : z∈ball (0 : ComplexVector n) A.radius) :
    ‖backgroundLogDetHessian A p z‖≤backgroundLogDetHessianBudget A ∧
      ‖fderiv ℝ (backgroundLogDetHessian A p) z‖≤backgroundLogDetHessianBudget A :=
  (Classical.choose_spec (exists_backgroundLogDetHessian_budget A)).2 p z hz

theorem backgroundLogDetHessian_lipschitz (A : BoundedChartFamily g) (p : M.Carrier)
    {z w : ComplexVector n} (hz : z∈ball (0 : ComplexVector n) A.radius)
    (hw : w∈ball (0 : ComplexVector n) A.radius) :
    ‖backgroundLogDetHessian A p z-backgroundLogDetHessian A p w‖≤
      backgroundLogDetHessianBudget A*‖z-w‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => ((A.backgroundLogDet_hessian_smooth p).contDiffAt
      (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    (fun y hy => (backgroundLogDetHessian_bounds A p hy).2) (convex_ball _ _) hw hz

def backgroundLogDetHessianHolder (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) : LocalHolderSpace (D2 n) P T γ :=
  spatialCoefficientHolder P hTime hγ hr (zero_le_one.trans (backgroundLogDetHessianBudget_ge_one P.charts))
    (backgroundLogDetHessian P.charts)
    (fun p => (P.charts.backgroundLogDet_hessian_smooth p).continuousOn.mono (ball_subset_ball P.radius_lt.le))
    (fun p _ hz => (backgroundLogDetHessian_bounds P.charts p ((ball_subset_ball P.radius_lt.le) hz)).1)
    (fun p _ hz _ hw => backgroundLogDetHessian_lipschitz P.charts p
      ((ball_subset_ball P.radius_lt.le) hz) ((ball_subset_ball P.radius_lt.le) hw))

def ricciMatrixBanach (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  ⟨localMapCLM (-(leviHessianCLM n)) (backgroundLogDetHessianHolder P hTime hγ hr)⟩

theorem ricciMatrixBanach_value (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) (q : LocalCylinder P T) :
    ricciMatrixBanach P hTime hγ hr q=pullbackRicci g (P.charts.chart q.1) q.2.1 := by
  change -leviHessianCLM n (fderiv ℝ (fderiv ℝ (P.charts.backgroundLogDet q.1)) q.2.1)=
    -leviC (P.charts.backgroundLogDet q.1) q.2.1
  congr 1
  exact (leviC_eq_leviHessianCLM (((P.charts.backgroundLogDet_smooth q.1).contDiffAt
    (isOpen_ball.mem_nhds ((ball_subset_ball P.radius_lt.le) q.2.1.property))).of_le (by simp))).symm

def ricciMatrixHolderBudget (A : BoundedChartFamily g) (γ : ℝ) : ℝ :=
  2*‖leviHessianCLM n‖*backgroundLogDetHessianBudget A*(1+(3:ℝ)^(1-γ))

theorem ricciMatrixBanach_norm_le (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) :
    ‖ricciMatrixBanach P hTime hγ hr‖≤ricciMatrixHolderBudget P.charts γ := by
  have hH : ‖backgroundLogDetHessianHolder P hTime hγ hr‖≤
      backgroundLogDetHessianBudget P.charts*(1+(3:ℝ)^(1-γ)) :=
    spatialCoefficientHolder_norm_le P hTime hγ hr _ _ _ _ _
  rw [norm_eq_twice]
  have hL := localMapElement_norm_le (-(leviHessianCLM n)) (backgroundLogDetHessianHolder P hTime hγ hr)
  rw [norm_neg] at hL
  exact (mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left hH (norm_nonneg _)))
    (by norm_num : (0:ℝ)≤2)).trans_eq (by unfold ricciMatrixHolderBudget; ring)

end Yau.LeafProofs.L17Aux
