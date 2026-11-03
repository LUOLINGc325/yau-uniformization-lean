import Yau.Proofs.F01PenalizedMajorantWeights
import Yau.Proofs.F01ComparisonMaximum
import Yau.Proofs.F01ScalarTimeMaximum

/-! The half-epsilon comparison gives a genuine positive quadratic
barrier for the same actual U and P. The shift also preserves the native
heat operator at every closed time face. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {A : Type*} {n : ℕ} {M : ComplexManifold n}

def shiftedMajorantComparison (D : ℝ) (n : ℕ) (U P : A → ℝ → ℝ)
    (Ξ u : A → ℝ) (c K ε : ℝ) (x : A) (t : ℝ) : ℝ :=
  comparisonFunction D n U P (penalizedMajorantWeight Ξ u c K ε) x t +
    (1 + |D * (majorantGrowthShift c K ε - majorantGrowthShift c K (ε / 2))|)

theorem shifted_majorant_comparison_positive
    (D : ℝ) (n : ℕ) (U P : A → ℝ → ℝ) (Ξ u : A → ℝ) (c K ε : ℝ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (x : A) (t : ℝ)
    (hhalf : 0 ≤ comparisonFunction D n U P
      (penalizedMajorantWeight Ξ u c K (ε / 2)) x t) :
    0 < shiftedMajorantComparison D n U P Ξ u c K ε x t ∧
      (D * ε / 2) * u x ^ 2 + 1 ≤ shiftedMajorantComparison D n U P Ξ u c K ε x t := by
  have he := comparisonFunction_epsilon_difference D ε n U P Ξ u
    (majorantGrowthShift c K) x t
  have hq := quadratic_lower_from_nonnegative_comparison he hhalf
  exact positive_shifted_quadratic (by positivity : 0 ≤ D * ε / 2) hq

theorem shifted_majorant_comparison_distance_lower
    (D : ℝ) (n : ℕ) (U P : A → ℝ → ℝ) (Ξ u : A → ℝ) (c K ε : ℝ)
    (hD : 0 < D) (hε : 0 < ε) (hK : 0 < K) (x : A) (t r : ℝ)
    (hr : 0 ≤ r) (hu : (1 + r) / K ≤ u x)
    (hhalf : 0 ≤ comparisonFunction D n U P
      (penalizedMajorantWeight Ξ u c K (ε / 2)) x t) :
    (D * ε / (2 * K ^ 2)) * (1 + r ^ 2) + 1 ≤
      shiftedMajorantComparison D n U P Ξ u c K ε x t := by
  have hbase := (shifted_majorant_comparison_positive D n U P Ξ u c K ε hD.le hε.le x t hhalf).2
  have hu0 : 0 ≤ (1 + r) / K := by positivity
  have hsq : ((1 + r) / K) ^ 2 ≤ u x ^ 2 :=
    (sq_le_sq₀ hu0 (hu0.trans hu)).mpr hu
  have hr2 : 1 + r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith
  have hbound : (D * ε / (2 * K ^ 2)) * (1 + r ^ 2) ≤ (D * ε / 2) * u x ^ 2 := by
    calc
      _ ≤ (D * ε / (2 * K ^ 2)) * (1 + r) ^ 2 :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = (D * ε / 2) * (((1 + r) / K) ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
  linarith

theorem shifted_majorant_comparison_smooth {U P : M.Carrier → ℝ → ℝ}
    {Ξ u : M.Carrier → ℝ} {I : Set ℝ}
    (hU : SmoothSpaceTime U I) (hP : SmoothSpaceTime P I)
    (hΞ : SmoothFn Ξ) (hu : SmoothFn u) (D c K ε : ℝ) :
    SmoothSpaceTime (shiftedMajorantComparison D n U P Ξ u c K ε) I := by
  have hφ : SmoothFn (penalizedMajorantWeight Ξ u c K ε) := fun a =>
    ((hΞ a).sub (contDiffOn_const.mul ((hu a).pow 2))).sub contDiffOn_const
  have hQ := comparisonFunction_smoothSpaceTime hU hP hφ D
  intro a
  exact (hQ a).add contDiffOn_const

theorem shifted_majorant_comparison_heat
    (h : ℝ → HermitianField M) {U P : M.Carrier → ℝ → ℝ}
    {Ξ u : M.Carrier → ℝ} {I : Set ℝ}
    (hU : SmoothSpaceTime U I) (hP : SmoothSpaceTime P I)
    (hΞ : SmoothFn Ξ) (hu : SmoothFn u) (D c K ε : ℝ)
    (x : M.Carrier) {t : ℝ} (ht : t ∈ I) (hI : UniqueDiffWithinAt ℝ I t) :
    fieldHeatWithin h I (fun s y => shiftedMajorantComparison D n U P Ξ u c K ε y s) x t =
      fieldHeatWithin h I (fun s y => comparisonFunction D n U P
        (penalizedMajorantWeight Ξ u c K ε) y s) x t := by
  have hφ : SmoothFn (penalizedMajorantWeight Ξ u c K ε) := fun a =>
    ((hΞ a).sub (contDiffOn_const.mul ((hu a).pow 2))).sub contDiffOn_const
  have hQ := comparisonFunction_smoothSpaceTime hU hP hφ D
  simpa only [shiftedMajorantComparison, sub_neg_eq_add] using
    fieldHeatWithin_sub_const h hQ
      (-(1 + |D * (majorantGrowthShift c K ε - majorantGrowthShift c K (ε / 2))|)) x ht hI

end Yau.NodeProofs.F01Aux
