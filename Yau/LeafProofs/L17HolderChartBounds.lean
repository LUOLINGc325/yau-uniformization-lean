import Yau.LeafProofs.L17HolderSpace
import Yau.LeafProofs.L17CommonChart

/-! Actual selected-chart and intrinsic parabolic differences. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17HolderAux

open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem chart_difference_bound {P : UniformChartPartition g} {T γ : ℝ}
    (u : HolderSpace P T γ) (p : P.centers) (q r : ChartCylinder P T) (hne : q ≠ r) :
    |holderFun u (chartPoint P T p r) - holderFun u (chartPoint P T p q)| ≤
      ‖u‖ * (parabolicDistance q r / P.radius) ^ γ := by
  let i : ChartPairs P T := ⟨p, ⟨(q, r), hne⟩⟩
  have h := weighted_difference_abs_le_norm u i
  rw [abs_mul, abs_of_pos (pairWeight_pos P T γ i)] at h
  change scaledPairWeight P γ q r *
    |holderFun u (chartPoint P T p r) - holderFun u (chartPoint P T p q)| ≤ ‖u‖ at h
  have hd := parabolicDistance_pos_of_ne hne
  have hprod : scaledPairWeight P γ q r *
      (‖u‖ * (parabolicDistance q r / P.radius) ^ γ) = ‖u‖ := by
    dsimp only [scaledPairWeight]
    rw [Real.div_rpow hd.le P.radius_pos.le]
    have hrpow := (Real.rpow_pos_of_pos P.radius_pos γ).ne'
    have hdpow := (Real.rpow_pos_of_pos hd γ).ne'
    field_simp
  by_contra hnot
  have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hnot)
    (show 0 < scaledPairWeight P γ q r from pairWeight_pos P T γ i)
  rw [hprod] at hlt
  exact (not_lt_of_ge h) hlt

def intrinsicParabolicDistance (g : HermitianField M) {T : ℝ} (a b : Cylinder M T) : ℝ :=
  inducedDistance g a.1 b.1 + Real.sqrt |(a.2 : ℝ) - (b.2 : ℝ)|

theorem intrinsicParabolicDistance_nonneg (g : HermitianField M) (hg : MetricSmooth g)
    {T : ℝ} (a b : Cylinder M T) : 0 ≤ intrinsicParabolicDistance g a b :=
  add_nonneg (L23Aux.inducedDistance_nonneg g hg _ _) (Real.sqrt_nonneg _)

theorem intrinsicParabolicDistance_pos_of_ne (g : HermitianField M) (hg : MetricSmooth g)
    {T : ℝ} {a b : Cylinder M T} (hne : a ≠ b) : 0 < intrinsicParabolicDistance g a b := by
  by_cases hxy : a.1 = b.1
  · have ht : (a.2 : ℝ) ≠ (b.2 : ℝ) := by
      intro heq
      exact hne (Prod.ext hxy (Subtype.ext heq))
    exact add_pos_of_nonneg_of_pos (L23Aux.inducedDistance_nonneg g hg _ _)
      (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr ht)))
  · let := L23Aux.metricSpaceOfField g hg
    have hd : 0 < inducedDistance g a.1 b.1 := by
      change 0 < dist a.1 b.1
      exact dist_pos.mpr hxy
    exact add_pos_of_pos_of_nonneg hd (Real.sqrt_nonneg _)

end Yau.LeafProofs.L17HolderAux
