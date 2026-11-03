import Yau.Blueprint.Analytic

/-! The actual polynomial-exponential comparison weight used in F03. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.F03Aux
open Yau Blueprint

variable {n : ℕ} {M : ComplexManifold n}

def comparisonWeight (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    (A : ℝ) (k : ℕ) (x : M.Carrier) (t : ℝ) : ℝ :=
  (u x) ^ (-(k : ℤ)) * Real.exp (-A * H x t / (u x) ^ 2)

theorem comparisonWeight_pos (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    (A : ℝ) (k : ℕ) (x : M.Carrier) (t : ℝ) (hu : 0 < u x) :
    0 < comparisonWeight u H A k x t :=
  mul_pos (zpow_pos hu _) (Real.exp_pos _)

theorem comparisonWeight_initial (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    (A : ℝ) (k : ℕ) (hH : ∀ x, H x 0 = 0) (x : M.Carrier) :
    comparisonWeight u H A k x 0 = (u x) ^ (-(k : ℤ)) := by
  simp only [comparisonWeight, hH x, mul_zero, zero_div, Real.exp_zero, mul_one]

/-- The size control of the glued correction gives polynomial comparability
with constants chosen independently of the point and physical time. -/
theorem comparisonWeight_bounds (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (k : ℕ)
    (x : M.Carrier) (t : ℝ) (hu : 0 < u x)
    (hH : |H x t| ≤ B * (u x) ^ 2) :
    (Real.exp (A * B))⁻¹ * (u x) ^ (-(k : ℤ)) ≤ comparisonWeight u H A k x t ∧
      comparisonWeight u H A k x t ≤ Real.exp (A * B) * (u x) ^ (-(k : ℤ)) := by
  have hu2 : 0 < (u x) ^ 2 := sq_pos_of_pos hu
  have hratio : |H x t / (u x) ^ 2| ≤ B := by
    rw [abs_div, abs_of_pos hu2]
    exact (div_le_iff₀ hu2).mpr hH
  have hexponent : |(-A * H x t) / (u x) ^ 2| ≤ A * B := by
    have hm := mul_le_mul_of_nonneg_left hratio hA
    simpa only [abs_mul, abs_neg, abs_of_nonneg hA, mul_div_assoc] using hm
  have hlow : Real.exp (-(A * B)) ≤ Real.exp (-A * H x t / (u x) ^ 2) :=
    Real.exp_le_exp.mpr (abs_le.mp hexponent).1
  have hhigh : Real.exp (-A * H x t / (u x) ^ 2) ≤ Real.exp (A * B) :=
    Real.exp_le_exp.mpr (abs_le.mp hexponent).2
  constructor
  · rw [← Real.exp_neg]
    simpa only [comparisonWeight, mul_comm] using
      mul_le_mul_of_nonneg_left hlow (zpow_nonneg hu.le _)
  · simpa only [comparisonWeight, mul_comm] using
      mul_le_mul_of_nonneg_left hhigh (zpow_nonneg hu.le _)

theorem comparisonWeight_hasDerivAt (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    (A : ℝ) (k : ℕ) (x : M.Carrier) {t d : ℝ} (hH : HasDerivAt (H x) d t) :
    HasDerivAt (comparisonWeight u H A k x)
      ((-A * d / (u x) ^ 2) * comparisonWeight u H A k x t) t := by
  have hd := (((hH.const_mul (-A)).div_const ((u x) ^ 2)).exp).const_mul
    ((u x) ^ (-(k : ℤ)))
  convert hd using 1
  · rfl
  · dsimp [comparisonWeight]
    ring

/-- The lower time estimate of the glued correction supplies exactly the
integrable upper time coefficient required for the actual comparison weight. -/
theorem comparisonWeight_time_bound (u : M.Carrier → ℝ) (H : M.Carrier → ℝ → ℝ)
    {A B D β t d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (k : ℕ) (x : M.Carrier) (hu : 1 ≤ u x) (ht : 0 < t)
    (hH : HasDerivAt (H x) d t)
    (hsize : |H x t| ≤ B * (u x) ^ 2 * t ^ β)
    (htime : H x t / t - D * u x ≤ d) :
    deriv (comparisonWeight u H A k x) t ≤
      (A * (B + D)) * (1 + t ^ (β - 1)) * comparisonWeight u H A k x t := by
  have hu0 : 0 < u x := zero_lt_one.trans_le hu
  have hu2 : 0 < (u x) ^ 2 := sq_pos_of_pos hu0
  rw [(comparisonWeight_hasDerivAt u H A k x hH).deriv]
  apply mul_le_mul_of_nonneg_right _ (comparisonWeight_pos u H A k x t hu0).le
  have hnegH : -(B * (u x) ^ 2 * t ^ β) ≤ H x t := (abs_le.mp hsize).1
  have hd : -(B * (u x) ^ 2 * t ^ β) / t - D * u x ≤ d :=
    (sub_le_sub_right (div_le_div_of_nonneg_right hnegH ht.le) _).trans htime
  have hpow : t ^ β / t = t ^ (β - 1) := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  have hInv : u x / (u x) ^ 2 ≤ 1 := by
    apply (div_le_one hu2).mpr
    nlinarith
  have hDbound : D * u x / (u x) ^ 2 ≤ D := by
    simpa only [mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left hInv hD
  have hmul := div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hd (neg_nonpos.mpr hA)) hu2.le
  have heq : -A * (-(B * (u x) ^ 2 * t ^ β) / t - D * u x) / (u x) ^ 2 =
      A * B * (t ^ β / t) + A * (D * u x / (u x) ^ 2) := by
    field_simp
    ring
  rw [heq, hpow] at hmul
  have hpospow : 0 ≤ t ^ (β - 1) := Real.rpow_nonneg ht.le _
  nlinarith [mul_le_mul_of_nonneg_left hDbound hA,
    mul_nonneg (mul_nonneg hA hB) (show (0 : ℝ) ≤ 1 by norm_num),
    mul_nonneg (mul_nonneg hA hD) hpospow]

end Yau.Proofs.F03Aux
