import Yau.LeafProofs.L10InteriorCalculus

/-! Numerical energy absorption, uniform before coefficients and functions. -/

noncomputable section
open scoped BigOperators

namespace Yau.LeafProofs

theorem elliptic_young {ell x y : ℝ} (hell : 0 < ell) :
    |x * y| ≤ ell / 2 * x^2 + y^2 / (2 * ell) := by
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * ell by positivity)).mp
  have h1 := sq_nonneg (ell*x-y)
  have h2 := sq_nonneg (ell*x+y)
  have he : (ell/2*x^2+y^2/(2*ell))*(2*ell) = ell^2*x^2+y^2 := by field_simp
  rw [he, abs_mul]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]; nlinarith
    · rw [abs_of_neg (lt_of_not_ge hy)]; nlinarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]; nlinarith
    · rw [abs_of_neg (lt_of_not_ge hy)]; nlinarith

def ellipticAbsorptionConstant (N : ℕ) (ell A B M : ℝ) : ℝ :=
  (N : ℝ) * (2 * N * A * M + B)^2 / (2 * ell) + 1

theorem ellipticAbsorptionConstant_pos (N : ℕ) {ell A B M : ℝ} (hell : 0 < ell) :
    0 < ellipticAbsorptionConstant N ell A B M := by
  unfold ellipticAbsorptionConstant
  positivity

theorem elliptic_finite_energy_absorption {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (c H d : ι → ℝ) (e w f ell A B M : ℝ)
    (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hc : ∀ i, |c i| ≤ B)
    (he : |e| ≤ 1) (hd : ∀ i, |d i| ≤ M)
    (hEll : ell * ∑ i, (e * H i)^2 ≤ ∑ i, ∑ j, a i j * (e * H i) * (e * H j)) :
    ell / 2 * (e^2 * ∑ i, (H i)^2) ≤
      ((∑ i, ∑ j, a i j * (e * H i) * (e * H j)) +
        (∑ i, (e * H i) * (2 * w * (∑ j, d j * a j i) - e * c i * w)) + e^2 * f * w) +
      ellipticAbsorptionConstant (Fintype.card ι) ell A B M * (w^2 + f^2) := by
  classical
  let N : ℝ := Fintype.card ι
  let K : ℝ := 2 * N * A * M + B
  let L : ι → ℝ := fun i => 2 * w * (∑ j, d j * a j i) - e * c i * w
  have hK : 0 ≤ K := by dsimp only [K, N]; positivity
  have hL (i : ι) : |L i| ≤ K * |w| := by
    have hs : |∑ j, d j * a j i| ≤ N * M * A := by
      calc
        _ ≤ ∑ j, |d j * a j i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : ι, M * A := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hd j) (ha j i) (abs_nonneg _) hM
        _ = _ := by simp [N]; ring
    calc
      _ ≤ |2 * w * (∑ j, d j * a j i)| + |e * c i * w| := abs_sub _ _
      _ ≤ 2 * |w| * (N * M * A) + 1 * B * |w| := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hs (by positivity)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul he (hc i) (abs_nonneg _) (by norm_num)) (abs_nonneg _)
      _ = _ := by dsimp only [K]; ring
  have hYoung (i : ι) :
      -(ell / 2 * (e * H i)^2 + K^2 * w^2 / (2 * ell)) ≤ (e * H i) * L i := by
    have hY := elliptic_young (x := e * H i) (y := L i) hell
    have hsq : (L i)^2 ≤ K^2 * w^2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg _) (hL i) 2
      simpa only [sq_abs, mul_pow] using hpow
    have hD := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2 * ell)
    linarith [neg_abs_le ((e * H i) * L i)]
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hYoung i)
  have he2 : e^2 ≤ 1 := by nlinarith [abs_nonneg e, sq_abs e]
  have hSource : -(w^2 + f^2) / 2 ≤ e^2 * f * w := by
    have hY := elliptic_young (x := f) (y := w) (ell := 1) (by norm_num)
    have habs : |e^2 * f * w| ≤ (w^2 + f^2) / 2 := by
      calc
        _ = e^2 * |f * w| := by rw [mul_assoc, abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ 1 * |f * w| := mul_le_mul_of_nonneg_right he2 (abs_nonneg _)
        _ ≤ _ := by nlinarith [hY]
    linarith [neg_abs_le (e^2 * f * w)]
  have hSq : (∑ i, (e * H i)^2) = e^2 * ∑ i, (H i)^2 := by
    simp only [mul_pow, Finset.mul_sum]
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hSum
  rw [hSq] at hEll
  dsimp only [ellipticAbsorptionConstant]
  change ell / 2 * (e^2 * ∑ i, (H i)^2) ≤ _ +
    (N * K^2 / (2 * ell) + 1) * (w^2 + f^2)
  have hC : 0 ≤ N * K^2 / (2 * ell) := by dsimp only [N]; positivity
  have hE : 0 ≤ e^2 * ∑ i, (H i)^2 := by positivity
  have hSum' : -(ell / 2 * (e^2 * ∑ i, (H i)^2) + N * (K^2 * w^2 / (2 * ell))) ≤
      ∑ i, (e * H i) * L i := by
    simpa only [← Finset.mul_sum, hSq, N] using hSum
  have hterm : N * (K^2 * w^2 / (2 * ell)) = (N * K^2 / (2 * ell)) * w^2 := by ring
  rw [hterm] at hSum'
  dsimp only [L] at hSum'
  nlinarith [mul_nonneg hC (sq_nonneg f), sq_nonneg w, sq_nonneg f]

def ellipticFiniteResidual {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (c H d : ι → ℝ) (e w f : ℝ) : ℝ :=
  (∑ i, ∑ j, a i j * (e * H i) * (e * H j)) +
    (∑ i, (e * H i) * (2 * w * (∑ j, d j * a j i) - e * c i * w)) + e^2 * f * w

theorem elliptic_complex_finite_energy_absorption {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (c d : ι → ℝ) (H : ι → ℂ) (w f : ℂ) (e ell A B M : ℝ)
    (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hc : ∀ i, |c i| ≤ B)
    (he : |e| ≤ 1) (hd : ∀ i, |d i| ≤ M)
    (hEll : ∀ v : ι → ℝ, ell * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, a i j * v i * v j) :
    ell / 2 * (e^2 * ∑ i, ‖H i‖^2) ≤
      (ellipticFiniteResidual a c (fun i => (H i).re) d e w.re f.re +
        ellipticFiniteResidual a c (fun i => (H i).im) d e w.im f.im) +
      ellipticAbsorptionConstant (Fintype.card ι) ell A B M * (‖w‖^2 + ‖f‖^2) := by
  have hr := elliptic_finite_energy_absorption a c (fun i => (H i).re) d e w.re f.re
    ell A B M hell hA hB hM ha hc he hd (hEll (fun i => e * (H i).re))
  have hi := elliptic_finite_energy_absorption a c (fun i => (H i).im) d e w.im f.im
    ell A B M hell hA hB hM ha hc he hd (hEll (fun i => e * (H i).im))
  have hnorm (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  have hsum : (∑ i, ‖H i‖^2) = (∑ i, (H i).re^2) + ∑ i, (H i).im^2 := by
    simp only [hnorm, Finset.sum_add_distrib]
  rw [hsum, hnorm w, hnorm f]
  change ell / 2 * (e^2 * ((∑ i, (H i).re^2) + ∑ i, (H i).im^2)) ≤ _
  dsimp only [ellipticFiniteResidual]
  linarith

theorem ellipticFiniteResidual_eq_test {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (c H d : ι → ℝ) (e w f : ℝ) :
    ellipticFiniteResidual a c H d e w f =
      (∑ i, (e^2 * H i + 2 * e * d i * w) * (∑ j, a i j * H j)) +
        e^2 * w * (f - ∑ i, c i * H i) := by
  classical
  have hprincipal : (∑ i, ∑ j, a i j * (e * H i) * (e * H j)) =
      ∑ i, (e^2 * H i) * (∑ j, a i j * H j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcross : (∑ i, (e * H i) * (2 * w * (∑ j, d j * a j i))) =
      ∑ i, (2 * e * d i * w) * (∑ j, a i j * H j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdrift : (∑ i, (e * H i) * (e * c i * w)) = e^2 * w * ∑ i, c i * H i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold ellipticFiniteResidual
  simp only [mul_sub, Finset.sum_sub_distrib, add_mul, Finset.sum_add_distrib]
  rw [hprincipal, hcross, hdrift]
  ring

end Yau.LeafProofs
