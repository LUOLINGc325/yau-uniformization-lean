import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Compact

/-!
Bernstein approximation on a symmetric interval, with the origin fixed and
with the original sharp derivative bound. This module uses only Mathlib.
-/

noncomputable section

open Set Filter Polynomial
open scoped Topology unitInterval

namespace Yau.NodeProofs.P06ClipBernstein

/-- A Bernstein polynomial with arbitrary real sampled values. -/
def bernsteinSum (n : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), C (a k) * bernsteinPolynomial ℝ n k

/-- The finite difference formula, including the two endpoint terms. -/
theorem bernsteinSum_derivative (n : ℕ) (a : ℕ → ℝ) :
    (bernsteinSum (n + 1) a).derivative =
      ∑ k ∈ Finset.range (n + 1),
        C (((n + 1 : ℕ) : ℝ) * (a (k + 1) - a k)) * bernsteinPolynomial ℝ n k := by
  classical
  have hshift :
      (∑ k ∈ Finset.range (n + 1), C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) =
        (∑ k ∈ Finset.range (n + 1), C (a k) * bernsteinPolynomial ℝ n k) -
          C (a 0) * bernsteinPolynomial ℝ n 0 := by
    have h := Finset.sum_range_succ' (fun k => C (a k) * bernsteinPolynomial ℝ n k) (n + 1)
    rw [Finset.sum_range_succ] at h
    simp only [bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n), mul_zero, add_zero] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  simp only [bernsteinSum, derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [Finset.sum_range_succ']
  simp only [bernsteinPolynomial.derivative_zero, bernsteinPolynomial.derivative_succ,
    Nat.add_sub_cancel]
  simp_rw [mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib]
  simp only [map_mul, map_sub, map_natCast, Nat.cast_add, Nat.cast_one, map_add, map_one]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hmul (b : ℕ → ℝ) :
      (∑ k ∈ Finset.range (n + 1), C (b k) * (n + 1) * bernsteinPolynomial ℝ n k) =
        (n + 1) * ∑ k ∈ Finset.range (n + 1), C (b k) * bernsteinPolynomial ℝ n k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hmul2 (b : ℕ → ℝ) :
      (∑ k ∈ Finset.range (n + 1), (n + 1) * C (b k) * bernsteinPolynomial ℝ n k) =
        (n + 1) * ∑ k ∈ Finset.range (n + 1), C (b k) * bernsteinPolynomial ℝ n k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hmul, hmul2, hmul2]
  have hmul' :
      (∑ k ∈ Finset.range (n + 1), C (a (k + 1)) * (n + 1) * bernsteinPolynomial ℝ n (k + 1)) =
        (n + 1) * ∑ k ∈ Finset.range (n + 1), C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hmul', hshift]
  ring

/-- The affine coordinate of `x` in `[-R,R]`. -/
def intervalCoordinate (R x : ℝ) : ℝ := (x + R) / (2 * R)

/-- Its genuine polynomial representative. -/
def intervalCoordinatePolynomial (R : ℝ) : Polynomial ℝ :=
  C ((2 * R)⁻¹) * (X + C R)

theorem intervalCoordinatePolynomial_eval (R x : ℝ) :
    (intervalCoordinatePolynomial R).eval x = intervalCoordinate R x := by
  simp [intervalCoordinatePolynomial, intervalCoordinate, div_eq_mul_inv, mul_comm]

/-- Sample the function after mapping `[0,1]` onto `[-R,R]`. -/
def intervalSamples (R : ℝ) (F : ℝ → ℝ) (n k : ℕ) : ℝ :=
  F (2 * R * ((k : ℝ) / n) - R)

/-- The uncorrected Bernstein polynomial on `[-R,R]`. -/
def intervalBernstein (R : ℝ) (F : ℝ → ℝ) (n : ℕ) : Polynomial ℝ :=
  (bernsteinSum n (intervalSamples R F n)).comp (intervalCoordinatePolynomial R)

/-- Degree `j+1` avoids the zero-degree sampling denominator; subtraction fixes zero. -/
def zeroFixedBernstein (R : ℝ) (F : ℝ → ℝ) (j : ℕ) : Polynomial ℝ :=
  intervalBernstein R F (j + 1) - C ((intervalBernstein R F (j + 1)).eval 0)

theorem zeroFixedBernstein_zero (R : ℝ) (F : ℝ → ℝ) (j : ℕ) :
    (zeroFixedBernstein R F j).eval 0 = 0 := by
  simp [zeroFixedBernstein]

/-- The affine coordinate lies in the unit interval, also at both endpoints. -/
theorem intervalCoordinate_mem {R x : ℝ} (hR : 0 < R) (hx : x ∈ Icc (-R) R) :
    intervalCoordinate R x ∈ Icc (0 : ℝ) 1 := by
  dsimp [intervalCoordinate]
  constructor
  · exact div_nonneg (by linarith [hx.1]) (by positivity)
  · apply (div_le_one (by positivity : 0 < 2 * R)).mpr
    linarith [hx.2]

/-- The exact coefficients of the derivative after affine rescaling. -/
def intervalSlope (R : ℝ) (F : ℝ → ℝ) (n k : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) *
    (intervalSamples R F (n + 1) (k + 1) - intervalSamples R F (n + 1) k) * (2 * R)⁻¹

theorem zeroFixedBernstein_derivative_eval (R : ℝ) (F : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    (zeroFixedBernstein R F n).derivative.eval x =
      ∑ k ∈ Finset.range (n + 1), intervalSlope R F n k *
        (bernsteinPolynomial ℝ n k).eval (intervalCoordinate R x) := by
  simp only [zeroFixedBernstein, derivative_sub, derivative_C, sub_zero,
    intervalBernstein, derivative_comp, bernsteinSum_derivative, eval_mul, eval_comp,
    intervalCoordinatePolynomial_eval, eval_finsetSum, eval_C]
  have hd : (intervalCoordinatePolynomial R).derivative.eval x = (2 * R)⁻¹ := by
    simp [intervalCoordinatePolynomial]
  rw [hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [intervalSlope]
  ring

theorem intervalSamples_step (R : ℝ) (n k : ℕ) :
    (2 * R * (((k + 1 : ℕ) : ℝ) / (n + 1)) - R) -
      (2 * R * ((k : ℝ) / (n + 1)) - R) = 2 * R / (n + 1) := by
  push_cast
  ring

theorem intervalSlope_abs_le_one {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : LipschitzWith 1 F) (n k : ℕ) : |intervalSlope R F n k| ≤ 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hstep : |intervalSamples R F (n + 1) (k + 1) - intervalSamples R F (n + 1) k| ≤
      2 * R / ((n + 1 : ℕ) : ℝ) := by
    have h := hF.dist_le_mul
      (2 * R * (((k + 1 : ℕ) : ℝ) / (n + 1)) - R)
      (2 * R * ((k : ℝ) / (n + 1)) - R)
    have hh : |F (2 * R * (((k + 1 : ℕ) : ℝ) / (n + 1)) - R) -
        F (2 * R * ((k : ℝ) / (n + 1)) - R)| ≤ |2 * R / (n + 1)| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, intervalSamples_step] using h
    have habs : |2 * R / (n + 1)| = 2 * R / (n + 1) :=
      abs_of_pos (div_pos (by positivity) (by positivity))
    simpa only [intervalSamples, Nat.cast_add, Nat.cast_one] using hh.trans (le_of_eq habs)
  calc
    |intervalSlope R F n k| = ((n + 1 : ℕ) : ℝ) *
        |intervalSamples R F (n + 1) (k + 1) - intervalSamples R F (n + 1) k| * (2 * R)⁻¹ := by
      simp only [intervalSlope, abs_mul, abs_of_pos hn,
        abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * R))]
    _ ≤ ((n + 1 : ℕ) : ℝ) * (2 * R / ((n + 1 : ℕ) : ℝ)) * (2 * R)⁻¹ := by
      gcongr
    _ = 1 := by field_simp

theorem bernsteinPolynomial_eval_nonneg (n k : ℕ) {s : ℝ} (hs : s ∈ Icc 0 1) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval s := by
  exact bernstein_nonneg (n := n) (ν := k) (x := ⟨s, hs⟩)

theorem bernsteinPolynomial_eval_sum (n : ℕ) (s : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval s) = 1 := by
  simpa only [eval_finsetSum, eval_one] using
    congrArg (fun p : Polynomial ℝ => p.eval s) (bernsteinPolynomial.sum ℝ n)

/-- Sharp Lipschitz control for exactly the zero-fixed polynomials above. -/
theorem zeroFixedBernstein_derivative_bound {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : LipschitzWith 1 F) (j : ℕ) {x : ℝ} (hx : x ∈ Icc (-R) R) :
    |(zeroFixedBernstein R F j).derivative.eval x| ≤ 1 := by
  rw [zeroFixedBernstein_derivative_eval]
  calc
    |∑ k ∈ Finset.range (j + 1), intervalSlope R F j k *
        (bernsteinPolynomial ℝ j k).eval (intervalCoordinate R x)| ≤
        ∑ k ∈ Finset.range (j + 1), |intervalSlope R F j k *
          (bernsteinPolynomial ℝ j k).eval (intervalCoordinate R x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (j + 1),
        (bernsteinPolynomial ℝ j k).eval (intervalCoordinate R x) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (bernsteinPolynomial_eval_nonneg j k (intervalCoordinate_mem hR hx))]
      exact mul_le_of_le_one_left (bernsteinPolynomial_eval_nonneg j k (intervalCoordinate_mem hR hx))
        (intervalSlope_abs_le_one hR hF j k)
    _ = 1 := bernsteinPolynomial_eval_sum j _

/-- Monotone data give nonnegative derivative coefficients in the same construction. -/
theorem intervalSlope_nonneg {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : Monotone F) (n k : ℕ) : 0 ≤ intervalSlope R F n k := by
  have hs := intervalSamples_step R n k
  have hn : (0 : ℝ) < n + 1 := by positivity
  have harg : 2 * R * ((k : ℝ) / (n + 1)) - R ≤
      2 * R * (((k + 1 : ℕ) : ℝ) / (n + 1)) - R := by
    linarith [div_pos (by positivity : 0 < 2 * R) hn]
  exact mul_nonneg (mul_nonneg (by positivity)
    (sub_nonneg.mpr (hF (by simpa only [Nat.cast_add, Nat.cast_one] using harg)))) (inv_nonneg.mpr (by positivity))

theorem zeroFixedBernstein_derivative_nonneg {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : Monotone F) (j : ℕ) {x : ℝ} (hx : x ∈ Icc (-R) R) :
    0 ≤ (zeroFixedBernstein R F j).derivative.eval x := by
  rw [zeroFixedBernstein_derivative_eval]
  exact Finset.sum_nonneg fun k hk => mul_nonneg (intervalSlope_nonneg hR hF j k)
    (bernsteinPolynomial_eval_nonneg j k (intervalCoordinate_mem hR hx))

/-- Continuous data on the unit interval obtained by affine transport. -/
def intervalFunction (R : ℝ) (F : ℝ → ℝ) (hF : Continuous F) : C(unitInterval, ℝ) :=
  ⟨fun s => F (2 * R * (s : ℝ) - R), hF.comp (by fun_prop)⟩

/-- Identification with Mathlib's Bernstein approximation, rather than an assumed limit. -/
theorem intervalBernstein_eval (R : ℝ) (F : ℝ → ℝ) (hF : Continuous F)
    (n : ℕ) {x : ℝ} (hx : intervalCoordinate R x ∈ Icc (0 : ℝ) 1) :
    (intervalBernstein R F n).eval x =
      bernsteinApproximation n (intervalFunction R F hF) ⟨intervalCoordinate R x, hx⟩ := by
  classical
  simp only [intervalBernstein, eval_comp, intervalCoordinatePolynomial_eval,
    bernsteinSum, eval_finsetSum, eval_mul, eval_C, Finset.sum_range,
    bernsteinApproximation.apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  change intervalSamples R F n k *
      (bernsteinPolynomial ℝ n k).eval (intervalCoordinate R x) =
    (bernsteinPolynomial ℝ n k).eval (intervalCoordinate R x) *
      F (2 * R * ((k : ℝ) / n) - R)
  exact mul_comm _ _

theorem intervalFunction_coordinate {R : ℝ} (hR : 0 < R) (F : ℝ → ℝ)
    (hF : Continuous F) {x : ℝ} (hx : intervalCoordinate R x ∈ Icc (0 : ℝ) 1) :
    intervalFunction R F hF ⟨intervalCoordinate R x, hx⟩ = F x := by
  change F (2 * R * ((x + R) / (2 * R)) - R) = F x
  congr 1
  field_simp
  ring

/-- The correction at zero contributes a second copy of the same uniform error. -/
theorem zeroFixedBernstein_uniform {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    TendstoUniformlyOn (fun j x => (zeroFixedBernstein R F j).eval x)
      F atTop (Icc (-R) R) := by
  classical
  let f : C(unitInterval, ℝ) := intervalFunction R F hF.continuous
  have hlim : Tendsto (fun j : ℕ => bernsteinApproximation (j + 1) f) atTop (𝓝 f) :=
    (bernsteinApproximation_uniform f).comp (tendsto_add_atTop_nat 1)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ j : ℕ in atTop, dist (bernsteinApproximation (j + 1) f) f < ε / 2 :=
    (Metric.tendsto_nhds.mp hlim) (ε / 2) (half_pos hε)
  filter_upwards [hev] with j hj x hx
  have hcx := intervalCoordinate_mem hR hx
  have hcz := intervalCoordinate_mem hR (show (0 : ℝ) ∈ Icc (-R) R by
    constructor <;> linarith)
  have hbound (y : ℝ) (hy : intervalCoordinate R y ∈ Icc (0 : ℝ) 1) :
      |(intervalBernstein R F (j + 1)).eval y - F y| < ε / 2 := by
    have hp := (ContinuousMap.dist_apply_le_dist (f := bernsteinApproximation (j + 1) f)
      (g := f) ⟨intervalCoordinate R y, hy⟩).trans_lt hj
    rw [intervalBernstein_eval R F hF.continuous (j + 1) hy]
    rw [← intervalFunction_coordinate hR F hF.continuous hy]
    exact hp
  have hxerr := hbound x hcx
  have hzerr := hbound 0 hcz
  rw [h0, sub_zero] at hzerr
  rw [Real.dist_eq, abs_sub_comm]
  simp only [zeroFixedBernstein, eval_sub, eval_C]
  calc
    |(intervalBernstein R F (j + 1)).eval x -
        (intervalBernstein R F (j + 1)).eval 0 - F x| =
      |((intervalBernstein R F (j + 1)).eval x - F x) -
        (intervalBernstein R F (j + 1)).eval 0| := by congr 1; ring
    _ ≤ |(intervalBernstein R F (j + 1)).eval x - F x| +
        |(intervalBernstein R F (j + 1)).eval 0| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxerr hzerr
    _ = ε := add_halves ε

/-- An explicit epsilon version convenient for choosing the degree separately on each compact set. -/
theorem zeroFixedBernstein_uniform_error {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j ≥ N, ∀ x ∈ Icc (-R) R,
      |(zeroFixedBernstein R F j).eval x - F x| ≤ ε := by
  have h := (Metric.tendstoUniformlyOn_iff.mp (zeroFixedBernstein_uniform hR hF h0)) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, fun j hj x hx => ?_⟩
  have hh := (hN j hj x hx).le
  simpa only [Real.dist_eq, abs_sub_comm] using hh

/-- Existence packaged with one fixed sequence and all three simultaneous properties. -/
theorem exists_zeroFixedBernstein {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    ∃ p : ℕ → Polynomial ℝ,
      (∀ j, (p j).eval 0 = 0) ∧
      (∀ j x, x ∈ Icc (-R) R → |(p j).derivative.eval x| ≤ 1) ∧
      TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R) :=
  ⟨zeroFixedBernstein R F, zeroFixedBernstein_zero R F,
    fun j _x hx => zeroFixedBernstein_derivative_bound hR hF j hx,
    zeroFixedBernstein_uniform hR hF h0⟩

/-- Monotone data retain the lower and upper derivative bounds on that same sequence. -/
theorem zeroFixedBernstein_derivative_mem_Icc {R : ℝ} {F : ℝ → ℝ} (hR : 0 < R)
    (hF : LipschitzWith 1 F) (hmono : Monotone F) (j : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-R) R) :
    (zeroFixedBernstein R F j).derivative.eval x ∈ Icc (0 : ℝ) 1 :=
  ⟨zeroFixedBernstein_derivative_nonneg hR hmono j hx,
    (le_abs_self _).trans (zeroFixedBernstein_derivative_bound hR hF j hx)⟩

end Yau.NodeProofs.P06ClipBernstein
