import Yau.Proofs.F04SeeleyWeights

noncomputable section

namespace Yau.F04Proof.Seeley

def triangular (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, j

theorem triangular_succ (k : ℕ) : triangular (k + 1) = triangular k + k :=
  Finset.sum_range_succ _ _

def leftDenominator (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (dyadic k - dyadic j)

theorem leftDenominator_pos (k : ℕ) : 0 < leftDenominator k := by
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (dyadic_strictMono (Finset.mem_range.mp hj))

theorem leftDenominator_succ (k : ℕ) :
    leftDenominator (k + 1) =
      dyadic k * leftDenominator k * (dyadic (k + 1) - 1) := by
  have hprod : (∏ j ∈ Finset.range k, (dyadic (k + 1) - dyadic (j + 1))) =
      dyadic k * leftDenominator k := by
    calc
      _ = ∏ j ∈ Finset.range k, (2 : ℝ) * (dyadic k - dyadic j) := by
        apply Finset.prod_congr rfl
        intro j _
        simp only [dyadic, pow_succ]
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [dyadic, leftDenominator]
  change (∏ j ∈ Finset.range (k + 1), (dyadic (k + 1) - dyadic j)) = _
  rw [Finset.prod_range_succ', hprod]
  simp only [dyadic, pow_zero]

theorem leftWeight_succ (k : ℕ) :
    leftWeight (k + 1) = leftWeight k *
      ((1 + dyadic k) / (dyadic k * (dyadic (k + 1) - 1))) := by
  have hratio (m : ℕ) : leftWeight m =
      (∏ j ∈ Finset.range m, (1 + dyadic j)) / leftDenominator m := by
    rw [leftWeight, Finset.prod_div_distrib]
    rfl
  rw [hratio, hratio, Finset.prod_range_succ, leftDenominator_succ]
  have hd := (leftDenominator_pos k).ne'
  have hk := (dyadic_pos k).ne'
  have h2k : 1 < dyadic (k + 1) := by
    have hs := dyadic_strictMono (show 0 < k + 1 by omega)
    simpa [dyadic] using hs
  field_simp

theorem leftWeight_step_bound (k : ℕ) :
    leftWeight (k + 1) ≤ leftWeight k * (2 / dyadic k) := by
  have hB := dyadic_ge_one k
  have hBp := dyadic_pos k
  have hCm : 0 < 2 * dyadic k - 1 := by linarith
  have hbase : (1 + dyadic k) / (2 * dyadic k - 1) ≤ 2 := by
    apply (div_le_iff₀ hCm).mpr
    linarith
  have hr : ((1 + dyadic k) / (dyadic k * (dyadic (k + 1) - 1))) ≤ 2 / dyadic k := by
    calc
      _ = ((1 + dyadic k) / (2 * dyadic k - 1)) / dyadic k := by
        rw [div_div]
        congr 1
        simp only [dyadic, pow_succ]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hbase hBp.le
  rw [leftWeight_succ]
  exact mul_le_mul_of_nonneg_left hr (leftWeight_pos k).le

/-- A Gaussian majorant with one extra dyadic factor is sufficient for every
moment; it avoids any division of natural triangular-number expressions. -/
theorem leftWeight_le (k : ℕ) : leftWeight k ≤ dyadic k / dyadic (triangular k) := by
  induction k with
  | zero => norm_num [leftWeight, dyadic, triangular]
  | succ k ih =>
    calc
      leftWeight (k + 1) ≤ leftWeight k * (2 / dyadic k) := leftWeight_step_bound k
      _ ≤ (dyadic k / dyadic (triangular k)) * (2 / dyadic k) :=
        mul_le_mul_of_nonneg_right ih (by positivity [dyadic_pos k])
      _ = dyadic (k + 1) / dyadic (triangular (k + 1)) := by
        rw [triangular_succ, dyadic_add]
        simp only [dyadic, pow_succ]
        field_simp
        simp [pow_add, mul_comm]

def weightMajorant (k : ℕ) : ℝ := 16 * dyadic k / dyadic (triangular k)

theorem weightMajorant_nonneg (k : ℕ) : 0 ≤ weightMajorant k := by
  unfold weightMajorant
  positivity [dyadic_pos k, dyadic_pos (triangular k)]

theorem finiteWeight_abs_le (N k : ℕ) : |finiteWeight N k| ≤ weightMajorant k := by
  by_cases hk : k ≤ N
  · rw [finiteWeight_factor N k hk, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_pos (leftWeight_pos k),
      abs_of_nonneg (le_trans zero_le_one (tailWeight_ge_one k (N - k)))]
    have h := mul_le_mul (leftWeight_le k) (tailWeight_le_sixteen k (N - k))
      (le_trans zero_le_one (tailWeight_ge_one k (N - k)))
      (by positivity [dyadic_pos k, dyadic_pos (triangular k)])
    convert h using 1
    dsimp [weightMajorant]
    ring
  · rw [finiteWeight_eq_zero_of_lt N k (Nat.lt_of_not_ge hk), abs_zero]
    exact weightMajorant_nonneg k

theorem seeleyWeight_abs_le (k : ℕ) : |seeleyWeight k| ≤ weightMajorant k := by
  apply le_of_tendsto ((finiteWeight_tendsto k).abs)
  exact Filter.Eventually.of_forall (fun N => finiteWeight_abs_le N k)

end Yau.F04Proof.Seeley
