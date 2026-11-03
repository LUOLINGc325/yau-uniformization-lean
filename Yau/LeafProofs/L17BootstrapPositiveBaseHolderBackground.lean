import Yau.LeafProofs.L17InverseMatrixHolder

/-! The actual background metric, constructed from its original entry bounds. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

namespace Yau.LeafProofs.L17BootstrapPositiveBaseHolderAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux

local instance positiveBaseBackgroundMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def backgroundEntryBudget (A : BoundedChartFamily g) : ℝ := 1+A.bound 0+A.bound 1

theorem backgroundEntryBudget_ge_one (A : BoundedChartFamily g) :
    1 ≤ backgroundEntryBudget A := by
  unfold backgroundEntryBudget
  linarith [A.bound_pos 0,A.bound_pos 1]

def backgroundEntry (A : BoundedChartFamily g) (i j : Fin n)
    (p : M.Carrier) (z : ComplexVector n) : ℂ := pullbackMatrix g (A.chart p) z i j

theorem backgroundEntry_bounds (A : BoundedChartFamily g) (i j : Fin n) (p : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius) :
    ‖backgroundEntry A i j p z‖ ≤ backgroundEntryBudget A ∧
      ‖fderiv ℝ (backgroundEntry A i j p) z‖ ≤ backgroundEntryBudget A := by
  have h0 : ‖backgroundEntry A i j p z‖ ≤ A.bound 0 := by
    simpa only [backgroundEntry,norm_iteratedFDeriv_zero] using A.coefficient_bound p 0 z hz i j
  have h1 : ‖fderiv ℝ (backgroundEntry A i j p) z‖ ≤ A.bound 1 := by
    change ‖fderiv ℝ (fun w : ComplexVector n => pullbackMatrix g (A.chart p) w i j) z‖ ≤ A.bound 1
    simpa only [norm_iteratedFDeriv_one] using A.coefficient_bound p 1 z hz i j
  constructor <;> apply le_trans (by assumption) <;>
    unfold backgroundEntryBudget <;> linarith [A.bound_pos 0,A.bound_pos 1]

theorem backgroundEntry_lipschitz (A : BoundedChartFamily g) (i j : Fin n) (p : M.Carrier)
    {z w : ComplexVector n} (hz : z ∈ ball 0 A.radius) (hw : w ∈ ball 0 A.radius) :
    ‖backgroundEntry A i j p z-backgroundEntry A i j p w‖ ≤
      backgroundEntryBudget A*‖z-w‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => ((A.coefficient_smooth p i j).contDiffAt
      (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    (fun y hy => (backgroundEntry_bounds A i j p hy).2) (convex_ball _ _) hw hz

def backgroundEntryHolder (P : UniformChartPartition g) {T gamma : ℝ}
    (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1)
    (i j : Fin n) : LocalHolderSpace ℂ P T gamma :=
  spatialCoefficientHolder P hTime hgamma hr
    (zero_le_one.trans (backgroundEntryBudget_ge_one P.charts))
    (backgroundEntry P.charts i j)
    (fun p => (P.charts.coefficient_smooth p i j).continuousOn.mono (ball_subset_ball P.radius_lt.le))
    (fun p z hz => (backgroundEntry_bounds P.charts i j p (z := z) ((ball_subset_ball P.radius_lt.le) hz)).1)
    (fun p z hz w hw => backgroundEntry_lipschitz P.charts i j p (z := z) (w := w)
      ((ball_subset_ball P.radius_lt.le) hz) ((ball_subset_ball P.radius_lt.le) hw))

theorem backgroundEntryHolder_norm_le (P : UniformChartPartition g) {T gamma : ℝ}
    (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1) (i j : Fin n) :
    ‖backgroundEntryHolder P hTime hgamma hr i j‖ ≤
      backgroundEntryBudget P.charts*(1+(3:ℝ)^(1-gamma)) :=
  spatialCoefficientHolder_norm_le P hTime hgamma hr _ _ _ _ _

def backgroundMatrixHolder (P : UniformChartPartition g) {T gamma : ℝ}
    (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1) :
    LocalHolderSpace (Matrix (Fin n) (Fin n) ℂ) P T gamma :=
  matrixHolderOfEntries (backgroundEntryHolder P hTime hgamma hr)

theorem backgroundMatrixHolder_value (P : UniformChartPartition g) {T gamma : ℝ}
    (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1)
    (q : LocalCylinder P T) :
    localFun _ (backgroundMatrixHolder P hTime hgamma hr) q =
      pullbackMatrix g (P.charts.chart q.1) q.2.1 :=
  matrixHolderOfEntries_value _ q

def backgroundMatrixBanach (P : UniformChartPartition g) {T gamma : ℝ}
    (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma :=
  ⟨backgroundMatrixHolder P hTime hgamma hr⟩

theorem backgroundMatrixBanach_value (P : UniformChartPartition g) {T gamma : ℝ}
    (hTime : T ≤ P.radius^2) (hgamma : gamma ≤ 1) (hr : P.radius ≤ 1)
    (q : LocalCylinder P T) :
    backgroundMatrixBanach P hTime hgamma hr q = pullbackMatrix g (P.charts.chart q.1) q.2.1 :=
  backgroundMatrixHolder_value P hTime hgamma hr q

end Yau.LeafProofs.L17BootstrapPositiveBaseHolderAux
