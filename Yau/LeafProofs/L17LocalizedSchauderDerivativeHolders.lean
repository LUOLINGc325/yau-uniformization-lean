import Yau.LeafProofs.L17LocalizedSchauderGlobalJetContinuity

open Set Metric
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def unitCylinderPoint (P : UniformChartPartition g) {T : ℝ} (q : ChartCylinder P T) : UnitCylinder n T :=
  (⟨P.radius⁻¹ • (q.1 : ComplexVector n),inv_radius_smul_mem_unit_ball P q.1.property⟩,q.2)

theorem unitCylinderPoint_continuous (P : UniformChartPartition g) (T : ℝ) :
    Continuous (unitCylinderPoint P (T := T)) := by
  have hSpace : Continuous (fun q : ChartCylinder P T => P.radius⁻¹ • (q.1 : ComplexVector n)) := by fun_prop
  exact (hSpace.subtype_mk _).prodMk continuous_snd

def rawGradientField (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : LocalCylinder P T) : D1 n :=
  globalUnitGradient P T v q.1 q.2.2 (P.radius⁻¹ • (q.2.1 : ComplexVector n))

def rawHessianField (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : LocalCylinder P T) : D2 n :=
  globalUnitHessian P T v q.1 q.2.2 (P.radius⁻¹ • (q.2.1 : ComplexVector n))

variable (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) {gamma B : ℝ}
    (hB : 0 ≤ B) (hLocal : LocalizedFourJetBounds P T gamma B v b)

include hTrue hB hLocal

theorem rawGradientField_continuous (hγ : 0 < gamma) : Continuous (rawGradientField P T v) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact (globalUnitGradient_continuous P T hT v D H b hTrue hB hLocal hγ p).comp
    (unitCylinderPoint_continuous P T)

theorem rawHessianField_continuous (hγ : 0 < gamma) : Continuous (rawHessianField P T v) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact (globalUnitHessian_continuous P T hT v D H b hTrue hB hLocal hγ p).comp
    (unitCylinderPoint_continuous P T)

theorem rawDerivativeField_norm_le (q : LocalCylinder P T) :
    ‖rawGradientField P T v q‖ ≤ (P.overlapBudget : ℝ)*B ∧
    ‖rawHessianField P T v q‖ ≤ (P.overlapBudget : ℝ)*B := by
  exact (globalUnit_derivative_bounds P T hT v D H b hTrue hB hLocal q.1 q.2.2 q.2.2
    (inv_radius_smul_mem_unit_ball P q.2.1.property) (inv_radius_smul_mem_unit_ball P q.2.1.property)).1

theorem rawDerivativeField_weighted_le (i : ChartPairs P T) :
    ‖pairWeight P T gamma i • (rawGradientField P T v (localRight P T i)-rawGradientField P T v (localLeft P T i))‖ ≤
        (2*(P.overlapBudget : ℝ))*B ∧
    ‖pairWeight P T gamma i • (rawHessianField P T v (localRight P T i)-rawHessianField P T v (localLeft P T i))‖ ≤
        (2*(P.overlapBudget : ℝ))*B := by
  have hh := (globalUnit_derivative_bounds P T hT v D H b hTrue hB hLocal i.1 i.2.val.1.2 i.2.val.2.2
    (inv_radius_smul_mem_unit_ball P i.2.val.1.1.property)
    (inv_radius_smul_mem_unit_ball P i.2.val.2.1.property)).2
  rw [unitParabolicDistance_inv_radius P i.2.val.1 i.2.val.2] at hh
  obtain ⟨hJ,hH⟩ := hh
  rw [norm_sub_rev] at hJ hH
  constructor
  · apply norm_weighted_pair_le P T gamma i
    simpa only [rawGradientField,localRight,localLeft] using hJ
  · apply norm_weighted_pair_le P T gamma i
    simpa only [rawHessianField,localRight,localLeft] using hH

def rawGradientHolder (hγ : 0 < gamma) : LocalHolderSpace (D1 n) P T gamma :=
  localOfBounds (D1 n) P T gamma (rawGradientField P T v)
    (rawGradientField_continuous P T hT v D H b hTrue hB hLocal hγ)
    ((P.overlapBudget : ℝ)*B) ((2*(P.overlapBudget : ℝ))*B)
    (fun q => (rawDerivativeField_norm_le P T hT v D H b hTrue hB hLocal q).1)
    (fun i => (rawDerivativeField_weighted_le P T hT v D H b hTrue hB hLocal i).1)

def rawHessianHolder (hγ : 0 < gamma) : LocalHolderSpace (D2 n) P T gamma :=
  localOfBounds (D2 n) P T gamma (rawHessianField P T v)
    (rawHessianField_continuous P T hT v D H b hTrue hB hLocal hγ)
    ((P.overlapBudget : ℝ)*B) ((2*(P.overlapBudget : ℝ))*B)
    (fun q => (rawDerivativeField_norm_le P T hT v D H b hTrue hB hLocal q).2)
    (fun i => (rawDerivativeField_weighted_le P T hT v D H b hTrue hB hLocal i).2)

theorem rawGradientHolder_value (hγ : 0 < gamma) :
    localFun (D1 n) (rawGradientHolder P T hT v D H b hTrue hB hLocal hγ) = rawGradientField P T v := rfl

theorem rawHessianHolder_value (hγ : 0 < gamma) :
    localFun (D2 n) (rawHessianHolder P T hT v D H b hTrue hB hLocal hγ) = rawHessianField P T v := rfl

theorem rawGradientHolder_norm_le (hγ : 0 < gamma) :
    ‖rawGradientHolder P T hT v D H b hTrue hB hLocal hγ‖ ≤ (2*(P.overlapBudget : ℝ))*B := by
  have hh := localOfBounds_norm_le (D1 n) P T gamma (rawGradientField P T v)
    (rawGradientField_continuous P T hT v D H b hTrue hB hLocal hγ)
    ((P.overlapBudget : ℝ)*B) ((2*(P.overlapBudget : ℝ))*B)
    (mul_nonneg (Nat.cast_nonneg _) hB) (mul_nonneg (by positivity) hB)
    (fun q => (rawDerivativeField_norm_le P T hT v D H b hTrue hB hLocal q).1)
    (fun i => (rawDerivativeField_weighted_le P T hT v D H b hTrue hB hLocal i).1)
  apply hh.trans (max_le _ le_rfl)
  nlinarith [mul_nonneg (Nat.cast_nonneg P.overlapBudget) hB]

theorem rawHessianHolder_norm_le (hγ : 0 < gamma) :
    ‖rawHessianHolder P T hT v D H b hTrue hB hLocal hγ‖ ≤ (2*(P.overlapBudget : ℝ))*B := by
  have hh := localOfBounds_norm_le (D2 n) P T gamma (rawHessianField P T v)
    (rawHessianField_continuous P T hT v D H b hTrue hB hLocal hγ)
    ((P.overlapBudget : ℝ)*B) ((2*(P.overlapBudget : ℝ))*B)
    (mul_nonneg (Nat.cast_nonneg _) hB) (mul_nonneg (by positivity) hB)
    (fun q => (rawDerivativeField_norm_le P T hT v D H b hTrue hB hLocal q).2)
    (fun i => (rawDerivativeField_weighted_le P T hT v D H b hTrue hB hLocal i).2)
  apply hh.trans (max_le _ le_rfl)
  nlinarith [mul_nonneg (Nat.cast_nonneg P.overlapBudget) hB]

end Yau.LeafProofs.L17LocalizedSchauderAux
