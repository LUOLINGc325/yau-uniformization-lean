import Yau.LeafProofs.L17InverseMatrixHolder
import Mathlib.Analysis.Normed.Operator.Mul

open Set Metric
open scoped Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux L17LocalHolderBanachAlgebraAux
local instance (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T γ : ℝ) (hT : 0<T)

def potentialLeviBanachCLM :
    SchauderSpace P T γ hT →L[ℝ] LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  (valueContinuousLinearEquiv (Matrix (Fin n) (Fin n) ℂ) P T γ).symm.toContinuousLinearMap.comp
    (potentialLeviHolderCLM P T γ hT)

theorem potentialLeviBanachCLM_value (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    potentialLeviBanachCLM P T γ hT u q = leviC (chartFunction u q.1 q.2.2) q.2.1 :=
  potentialLeviHolderCLM_value P T γ hT u q.1 q.2.1 q.2.2

theorem potentialLeviBanachCLM_norm_le (u : SchauderSpace P T γ hT) :
    ‖potentialLeviBanachCLM P T γ hT u‖ ≤ (2*‖leviHessianCLM n‖)*‖u‖ := by
  change ‖(⟨potentialLeviHolderCLM P T γ hT u⟩ : LocalHolderBanach _ P T γ)‖ ≤ _
  rw [norm_ofLocal]
  exact (mul_le_mul_of_nonneg_left (potentialLeviHolderCLM_norm_le P T γ hT u)
    (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

def localMatrixLeftMulLinearMap
    (a : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ →ₗ[ℝ]
      LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ where
  toFun b := a*b
  map_add' b c := mul_add a b c
  map_smul' c b := by
    apply L17LocalHolderBanachAlgebraAux.ext
    intro q
    change a q*(c • b q)=c • (a q*b q)
    exact mul_smul_comm c (a q) (b q)

def localMatrixLeftMulCLM
    (a : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ →L[ℝ]
      LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  (localMatrixLeftMulLinearMap P T γ a).mkContinuous ‖a‖ (norm_mul_le a)

def normalizedPotentialCLM (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1) :
    SchauderSpace P T γ hT →L[ℝ] LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T γ :=
  (localMatrixLeftMulCLM P T γ (inverseMatrixBanach P hTime hγ hr)).comp
    (potentialLeviBanachCLM P T γ hT)

theorem normalizedPotentialCLM_value (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T γ hT) (q : LocalCylinder P T) :
    normalizedPotentialCLM P T γ hT hTime hγ hr u q =
      (pullbackMatrix g (P.charts.chart q.1) q.2.1)⁻¹*leviC (chartFunction u q.1 q.2.2) q.2.1 := by
  change inverseMatrixBanach P hTime hγ hr q*potentialLeviBanachCLM P T γ hT u q = _
  rw [inverseMatrixBanach_value,potentialLeviBanachCLM_value]

theorem normalizedPotentialCLM_norm_le (hTime : T≤P.radius^2) (hγ : γ≤1) (hr : P.radius≤1)
    (u : SchauderSpace P T γ hT) :
    ‖normalizedPotentialCLM P T γ hT hTime hγ hr u‖ ≤
      (4*inverseMatrixHolderBudget P.charts γ*‖leviHessianCLM n‖)*‖u‖ := by
  apply (norm_mul_le (inverseMatrixBanach P hTime hγ hr) (potentialLeviBanachCLM P T γ hT u)).trans
  exact (mul_le_mul (inverseMatrixBanach_norm_le P hTime hγ hr)
    (potentialLeviBanachCLM_norm_le P T γ hT u) (norm_nonneg _)
    (mul_nonneg (by norm_num) (zero_le_one.trans (inverseMatrixHolderBudget_ge_one P.charts γ)))).trans_eq (by ring)

end Yau.LeafProofs.L17Aux
