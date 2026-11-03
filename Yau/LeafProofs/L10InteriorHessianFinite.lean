import Yau.LeafProofs.L10InteriorHessianAlgebra

/-! The second-derivative estimate uses no derivative of the source or drift. -/

noncomputable section
open scoped BigOperators

namespace Yau.LeafProofs

def ellipticHessianFiniteResidual {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (E : ι → ι → ι → ℝ) (c d G : ι → ℝ)
    (H : ι → ι → ℝ) (e f : ℝ) : ℝ :=
  (∑ k, ∑ i, (e^2 * H k i + 2 * e * d i * G k) *
    ((∑ j, a i j * H k j) + ∑ j, E k i j * G j)) -
  ∑ k, (e^2 * H k k + 2 * e * d k * G k) * (f - ∑ j, c j * G j)

theorem elliptic_hessian_finite_absorption {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (E : ι → ι → ι → ℝ) (c d G : ι → ℝ)
    (H : ι → ι → ℝ) (e f ell A B M : ℝ)
    (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hE : ∀ k i j, |E k i j| ≤ A)
    (hc : ∀ i, |c i| ≤ B) (hd : ∀ i, |d i| ≤ M) (he : |e| ≤ 1)
    (hEll : ∀ v : ι → ℝ, ell * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, a i j * v i * v j) :
    ell / 2 * (e^2 * ∑ k, ∑ i, (H k i)^2) ≤
      ellipticHessianFiniteResidual a E c d G H e f +
        ellipticHessianAbsorptionConstant (Fintype.card ι) ell A B M *
          ((∑ i, (G i)^2) + f^2) := by
  classical
  let N : ℝ := Fintype.card ι
  let U : ℝ := Real.sqrt (∑ k, ∑ i, (H k i)^2)
  let V : ℝ := Real.sqrt (∑ i, (G i)^2)
  let X : ℝ := |e| * U
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hX : 0 ≤ X := mul_nonneg (abs_nonneg _) hU
  have hU2 : U^2 = ∑ k, ∑ i, (H k i)^2 := Real.sq_sqrt (by positivity)
  have hV2 : V^2 = ∑ i, (G i)^2 := Real.sq_sqrt (by positivity)
  have hX2 : X^2 = e^2 * ∑ k, ∑ i, (H k i)^2 := by
    simp only [X, mul_pow, sq_abs, hU2]
  have hGH (k i : ι) : |H k i| ≤ U := by
    have h1 : (H k i)^2 ≤ ∑ j, (H k j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (H k j)) (Finset.mem_univ i)
    have h2 : (∑ j, (H k j)^2) ≤ ∑ l, ∑ j, (H l j)^2 :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun j _ => sq_nonneg (H l j))
        (Finset.mem_univ k)
    nlinarith [sq_abs (H k i), abs_nonneg (H k i)]
  have hGG (i : ι) : |G i| ≤ V := by
    have h1 : (G i)^2 ≤ ∑ j, (G j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (G j)) (Finset.mem_univ i)
    nlinarith [sq_abs (G i), abs_nonneg (G i)]
  have hFlux (k i : ι) : |∑ j, a i j * H k j| ≤ N * A * U := by
    calc
      _ ≤ ∑ j, |a i j * H k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, A * U := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (ha i j) (hGH k j) (abs_nonneg _) hA
      _ = _ := by simp [N]; ring
  have hError (k i : ι) : |∑ j, E k i j * G j| ≤ N * A * V := by
    calc
      _ ≤ ∑ j, |E k i j * G j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, A * V := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hE k i j) (hGG j) (abs_nonneg _) hA
      _ = _ := by simp [N]; ring
  have hDrift : |f - ∑ j, c j * G j| ≤ |f| + N * B * V := by
    apply (abs_sub _ _).trans
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ j, |c j * G j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, B * V := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hc j) (hGG j) (abs_nonneg _) hB
      _ = _ := by simp [N]; ring
  have he2 : |e|^2 ≤ |e| := by nlinarith [abs_nonneg e]
  let Q : ℝ := (N * A + 2 * N * M * A) * X * V + 2 * N * M * A * V^2
  let T : ι → ι → ℝ := fun k i => (e^2 * H k i + 2 * e * d i * G k) *
    ((∑ j, a i j * H k j) + ∑ j, E k i j * G j)
  let P : ι → ι → ℝ := fun k i => ∑ j, a i j * (e * H k i) * (e * H k j)
  let S : ι → ℝ := fun k => (e^2 * H k k + 2 * e * d k * G k) * (f - ∑ j, c j * G j)
  have hP (k i : ι) : P k i = e^2 * H k i * ∑ j, a i j * H k j := by
    dsimp only [P]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTerm (k i : ι) : -Q ≤ T k i - P k i := by
    have h1 : |e^2 * H k i * (∑ j, E k i j * G j)| ≤ X * (N * A * V) := by
      calc
        _ = |e|^2 * |H k i| * |∑ j, E k i j * G j| := by simp only [abs_mul, abs_pow]
        _ ≤ |e| * U * (N * A * V) := by
          gcongr <;> first | exact hGH k i | exact hError k i
        _ = _ := rfl
    have h2 : |2 * e * d i * G k * (∑ j, a i j * H k j)| ≤ 2 * N * M * A * X * V := by
      calc
        _ = 2 * |e| * |d i| * |G k| * |∑ j, a i j * H k j| := by
          simp only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        _ ≤ 2 * |e| * M * V * (N * A * U) := by
          gcongr <;> first | exact hd i | exact hGG k | exact hFlux k i
        _ = _ := by dsimp only [X]; ring
    have h3 : |2 * e * d i * G k * (∑ j, E k i j * G j)| ≤ 2 * N * M * A * V^2 := by
      calc
        _ = 2 * |e| * |d i| * |G k| * |∑ j, E k i j * G j| := by
          simp only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        _ ≤ 2 * 1 * M * V * (N * A * V) := by
          gcongr <;> first | exact hd i | exact hGG k | exact hError k i
        _ = _ := by ring
    have hAbs : |T k i - P k i| ≤ Q := by
      rw [hP]
      calc
        _ = |e^2 * H k i * (∑ j, E k i j * G j) +
            2 * e * d i * G k * (∑ j, a i j * H k j) +
            2 * e * d i * G k * (∑ j, E k i j * G j)| := by dsimp only [T]; congr 1; ring
        _ ≤ |e^2 * H k i * (∑ j, E k i j * G j)| +
            |2 * e * d i * G k * (∑ j, a i j * H k j)| +
            |2 * e * d i * G k * (∑ j, E k i j * G j)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ X * (N * A * V) + 2 * N * M * A * X * V + 2 * N * M * A * V^2 :=
          add_le_add (add_le_add h1 h2) h3
        _ = _ := by dsimp only [Q]; ring
    linarith [neg_abs_le (T k i - P k i)]
  have hSource (k : ι) : S k ≤ (X + 2 * M * V) * (|f| + N * B * V) := by
    have ht : |e^2 * H k k + 2 * e * d k * G k| ≤ X + 2 * M * V := by
      apply (abs_add_le _ _).trans
      apply add_le_add
      · calc
          _ = |e|^2 * |H k k| := by rw [abs_mul, abs_pow]
          _ ≤ |e| * U := mul_le_mul he2 (hGH k k) (abs_nonneg _) (abs_nonneg _)
      · calc
          _ = 2 * |e| * |d k| * |G k| := by
            simp only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
          _ ≤ 2 * 1 * M * V := by
            gcongr <;> first | exact hd k | exact hGG k
          _ = _ := by ring
    exact (le_abs_self (S k)).trans (by
      dsimp only [S]
      rw [abs_mul]
      exact mul_le_mul ht hDrift (abs_nonneg _) (by positivity))
  have hPrincipal : ell * X^2 ≤ ∑ k, ∑ i, P k i := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hEll (fun i => e * H k i))
    simpa only [P, mul_pow, ← Finset.mul_sum, ← hX2] using hsum
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hTerm k i))
  have hSumSource := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hSource k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_sub_distrib] at hSum hSumSource
  have hAbsorb := elliptic_hessian_scalar_absorption hN hell hA hB hM hX hV (abs_nonneg f)
  have hEq : N^2 * Q + N * ((X + 2 * M * V) * (|f| + N * B * V)) =
      (N^3 * A + 2 * N^3 * M * A) * X * V + 2 * N^3 * M * A * V^2 +
        N * X * (|f| + N * B * V) + 2 * N * M * V * (|f| + N * B * V) := by
    dsimp only [Q]
    ring
  rw [← hEq] at hAbsorb
  rw [← hX2, ← hV2, ← sq_abs f]
  change ell / 2 * X^2 ≤ ((∑ k, ∑ i, T k i) - ∑ k, S k) +
    ellipticHessianAbsorptionConstant N ell A B M * (V^2 + |f|^2)
  have hSum' : -(N^2 * Q) ≤ (∑ k, ∑ i, T k i) - ∑ k, ∑ i, P k i := by
    convert hSum using 1
    dsimp only [N]
    ring
  change (∑ k, S k) ≤ N * ((X + 2 * M * V) * (|f| + N * B * V)) at hSumSource
  nlinarith [hSum']

end Yau.LeafProofs
