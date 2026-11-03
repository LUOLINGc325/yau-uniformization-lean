import Yau.LeafProofs.L17RicciMatrixHolder
import Yau.LeafProofs.L17AffineLogDetDerivative
import Yau.LeafProofs.L17TimeScalarAction

open Set Metric
open scoped Matrix.Norms.Frobenius ContDiff
noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance ricciForcingTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def normalizedRicciBanach (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  localMatrixLeftMulCLM P T γ (inverseMatrixBanach P hTime hγ hr)
    (ricciMatrixBanach P hTime hγ hr)

theorem normalizedRicciBanach_value (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) (q : LocalCylinder P T) :
    normalizedRicciBanach P hTime hγ hr q=
      (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹*pullbackRicci g (P.charts.chart q.1) q.2.1 := by
  change inverseMatrixBanach P hTime hγ hr q*ricciMatrixBanach P hTime hγ hr q=_
  rw [inverseMatrixBanach_value,ricciMatrixBanach_value]

def normalizedRicciBudget (A : BoundedChartFamily g) (γ : ℝ) : ℝ :=
  2*inverseMatrixHolderBudget A γ*ricciMatrixHolderBudget A γ

theorem normalizedRicciBanach_norm_le (P : UniformChartPartition g) {T γ : ℝ}
    (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) :
    ‖normalizedRicciBanach P hTime hγ hr‖≤normalizedRicciBudget P.charts γ := by
  apply (norm_mul_le (inverseMatrixBanach P hTime hγ hr) (ricciMatrixBanach P hTime hγ hr)).trans
  exact mul_le_mul (inverseMatrixBanach_norm_le P hTime hγ hr) (ricciMatrixBanach_norm_le P hTime hγ hr)
    (norm_nonneg _) (mul_nonneg (by norm_num) (zero_le_one.trans (inverseMatrixHolderBudget_ge_one P.charts γ)))

def timeRicciBanach (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  timeScalarActionCLM P hT hγ (hγ1.trans (by norm_num)) hr (normalizedRicciBanach P hTime hγ1 hr)

theorem timeRicciBanach_value (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)
    (q : LocalCylinder P T) :
    timeRicciBanach P hT hTime hγ hγ1 hr q=(q.2.2 : ℝ) •
      ((pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹*pullbackRicci g (P.charts.chart q.1) q.2.1) := by
  rw [timeRicciBanach,timeScalarActionCLM_value,normalizedRicciBanach_value]

theorem timeRicciBanach_norm_le (P : UniformChartPartition g) {T γ : ℝ}
    (hT : 0<T) (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1) :
    ‖timeRicciBanach P hT hTime hγ hγ1 hr‖≤(2*normalizedRicciBudget P.charts γ)*T^(1-γ/2) := by
  have hTone : T≤1 := hTime.trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0≤1+P.radius by linarith [P.radius_pos])])
  exact (timeScalarActionCLM_norm_le P hT hTone hγ (hγ1.trans (by norm_num)) hr _).trans
    ((mul_le_mul_of_nonneg_left (normalizedRicciBanach_norm_le P hTime hγ1 hr)
      (by positivity)).trans_eq (by ring))

def normalizedMetricPerturbation (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
    (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T γ hT) : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  normalizedPotentialCLM P T γ hT hTime hγ1 hr u-timeRicciBanach P hT hTime hγ hγ1 hr

theorem normalizedMetricPerturbation_value (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
    (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u q =
      (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹*
        (leviC (chartFunction u q.1 q.2.2) q.2.1-(q.2.2 : ℂ) • pullbackRicci g (P.charts.chart q.1) q.2.1) := by
  change normalizedPotentialCLM P T γ hT hTime hγ1 hr u q-timeRicciBanach P hT hTime hγ hγ1 hr q=_
  rw [normalizedPotentialCLM_value,timeRicciBanach_value,matrixRealScalar_eq_complexScalar,Matrix.mul_sub,Matrix.mul_smul]

theorem normalizedMetricPerturbation_norm_le (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
    (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T γ hT) :
    ‖normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr u‖≤
      (4*inverseMatrixHolderBudget P.charts γ*‖leviHessianCLM n‖)*‖u‖+
        (2*normalizedRicciBudget P.charts γ)*T^(1-γ/2) :=
  (norm_sub_le _ _).trans (add_le_add (normalizedPotentialCLM_norm_le P T γ hT hTime hγ1 hr u)
    (timeRicciBanach_norm_le P hT hTime hγ hγ1 hr))

theorem normalizedMetricPerturbation_contDiff (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)
    (hTime : T≤P.radius^2) (hγ : 0≤γ) (hγ1 : γ≤1) (hr : P.radius≤1) :
    ContDiff ℝ ∞ (normalizedMetricPerturbation P T γ hT hTime hγ hγ1 hr) :=
  (normalizedPotentialCLM P T γ hT hTime hγ1 hr).contDiff.sub contDiff_const

end Yau.LeafProofs.L17Aux
