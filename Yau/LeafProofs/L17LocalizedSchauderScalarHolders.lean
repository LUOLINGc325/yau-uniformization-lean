import Yau.LeafProofs.L17LocalizedSchauderLocalEstimates

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scaledLocalizedTerm_weighted_bound (P : UniformChartPartition g) (T gamma B : ℝ)
    (v b : P.centers → ComplexVector n × Time T → ℝ)
    (hLocal : LocalizedFourJetBounds P T gamma B v b) (p : P.centers) (i : ChartPairs P T) :
    |pairWeight P T gamma i*((P.radius^2)⁻¹ • localizedTerm P T p (v p) (chartRight P T i)-
      (P.radius^2)⁻¹ • localizedTerm P T p (v p) (chartLeft P T i))| ≤ B := by
  have hh := (hLocal.1 p i.1 i.2.val.1.2 i.2.val.2.2
    (P.radius⁻¹ • (i.2.val.1.1 : ComplexVector n)) (P.radius⁻¹ • (i.2.val.2.1 : ComplexVector n))
    (inv_radius_smul_mem_unit_ball P i.2.val.1.1.property)
    (inv_radius_smul_mem_unit_ball P i.2.val.2.1.property) 0 (by norm_num)).2
  rw [norm_iteratedFDeriv_zero_sub] at hh
  simp only [unitLocalizedTerm,unitValue,smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul] at hh
  rw [unitParabolicDistance_inv_radius P i.2.val.1 i.2.val.2,norm_sub_rev] at hh
  have hWeighted := norm_weighted_pair_le P T gamma i
    ((P.radius^2)⁻¹ • localizedTerm P T p (v p) (chartRight P T i))
    ((P.radius^2)⁻¹ • localizedTerm P T p (v p) (chartLeft P T i))
    (by simpa only [chartRight,chartLeft,chartPoint] using hh)
  simpa only [Real.norm_eq_abs,smul_eq_mul] using hWeighted

theorem timeLocalizedTerm_weighted_bound (P : UniformChartPartition g) (T gamma B : ℝ)
    (v b : P.centers → ComplexVector n × Time T → ℝ)
    (hLocal : LocalizedFourJetBounds P T gamma B v b) (p : P.centers) (i : ChartPairs P T) :
    |pairWeight P T gamma i*(localizedTerm P T p (b p) (chartRight P T i)-
      localizedTerm P T p (b p) (chartLeft P T i))| ≤ B := by
  have hh := hLocal.2 p i.1 i.2.val.1.2 i.2.val.2.2
    (P.radius⁻¹ • (i.2.val.1.1 : ComplexVector n)) (P.radius⁻¹ • (i.2.val.2.1 : ComplexVector n))
    (inv_radius_smul_mem_unit_ball P i.2.val.1.1.property)
    (inv_radius_smul_mem_unit_ball P i.2.val.2.1.property)
  simp only [smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul] at hh
  rw [unitParabolicDistance_inv_radius P i.2.val.1 i.2.val.2,abs_sub_comm] at hh
  have hWeighted := norm_weighted_pair_le P T gamma i
    (localizedTerm P T p (b p) (chartRight P T i)) (localizedTerm P T p (b p) (chartLeft P T i))
    (by simpa only [Real.norm_eq_abs,chartRight,chartLeft,chartPoint] using hh)
  simpa only [Real.norm_eq_abs,smul_eq_mul] using hWeighted

variable (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) {gamma F B : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hBounds : LocalScaledJetBounds P T gamma F v D H b)
    (hLocal : LocalizedFourJetBounds P T gamma B v b)

include hF hBounds

theorem scaledLocalizedTerm_abs_le (p : P.centers) (q : Cylinder M T) :
    |(P.radius^2)⁻¹ • localizedTerm P T p (v p) q| ≤ F := by
  have hh := localizedTerm_abs_le P T p (v p) (P.radius^2*F) (mul_nonneg (sq_nonneg _) hF)
    (fun z hz t => (hBounds.1 p (z,t) hz).1) q
  simpa only [Real.norm_eq_abs] using norm_inv_smul_le_of_le (sq_pos_of_pos P.radius_pos)
    (localizedTerm P T p (v p) q) (by simpa only [Real.norm_eq_abs] using hh)

def rawValueHolder : HolderSpace P T gamma :=
  supportedSumHolder P T gamma (fun p q => (P.radius^2)⁻¹ • localizedTerm P T p (v p) q)
    (fun p => (localizedTerm_continuous P T p (v p) (hTrue.1 p).1).const_smul ((P.radius^2)⁻¹))
    (fun p q hq => by rw [localizedTerm_zero_of_not_cover P T p (v p) q hq,smul_zero])
    F B hF hB (scaledLocalizedTerm_abs_le P T v D H b hF hBounds)
    (scaledLocalizedTerm_weighted_bound P T gamma B v b hLocal)

def actualTimeHolder : HolderSpace P T gamma :=
  supportedSumHolder P T gamma (fun p => localizedTerm P T p (b p))
    (fun p => localizedTerm_continuous P T p (b p) (hTrue.1 p).2.2.2)
    (fun p q hq => localizedTerm_zero_of_not_cover P T p (b p) q hq)
    F B hF hB
    (fun p q => localizedTerm_abs_le P T p (b p) F hF
      (fun z hz t => (hBounds.1 p (z,t) hz).2.2.2) q)
    (timeLocalizedTerm_weighted_bound P T gamma B v b hLocal)

theorem rawValueHolder_value (q : Cylinder M T) :
    holderFun (rawValueHolder P T hT v D H b hTrue hF hB hBounds hLocal) q =
      (P.radius^2)⁻¹ • globalSum P T v q :=
  supported_finsum_smul P T (fun p => localizedTerm P T p (v p)) ((P.radius^2)⁻¹)
    (fun p q hq => localizedTerm_zero_of_not_cover P T p (v p) q hq) q

theorem actualTimeHolder_value (q : Cylinder M T) :
    holderFun (actualTimeHolder P T hT v D H b hTrue hF hB hBounds hLocal) q = globalSum P T b q := rfl

theorem rawValueHolder_norm_le :
    ‖rawValueHolder P T hT v D H b hTrue hF hB hBounds hLocal‖ ≤
      max ((P.overlapBudget : ℝ)*F) ((2*(P.overlapBudget : ℝ))*B) :=
  supportedSumHolder_norm_le _ _ _ _ _ _ _ _ _ _ _ _

theorem actualTimeHolder_norm_le :
    ‖actualTimeHolder P T hT v D H b hTrue hF hB hBounds hLocal‖ ≤
      max ((P.overlapBudget : ℝ)*F) ((2*(P.overlapBudget : ℝ))*B) :=
  supportedSumHolder_norm_le _ _ _ _ _ _ _ _ _ _ _ _

end Yau.LeafProofs.L17LocalizedSchauderAux
